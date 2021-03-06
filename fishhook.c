// Copyright (c) 2013, Facebook, Inc.
// All rights reserved.
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//   * Redistributions of source code must retain the above copyright notice,
//     this list of conditions and the following disclaimer.
//   * Redistributions in binary form must reproduce the above copyright notice,
//     this list of conditions and the following disclaimer in the documentation
//     and/or other materials provided with the distribution.
//   * Neither the name Facebook nor the names of its contributors may be used to
//     endorse or promote products derived from this software without specific
//     prior written permission.
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
// SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#include "fishhook.h"

#include <dlfcn.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <mach/mach.h>
#include <mach/vm_map.h>
#include <mach/vm_region.h>
#include <mach-o/dyld.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>

#ifdef __LP64__
typedef struct mach_header_64 mach_header_t;
typedef struct segment_command_64 segment_command_t;
typedef struct section_64 section_t;
typedef struct nlist_64 nlist_t;
#define LC_SEGMENT_ARCH_DEPENDENT LC_SEGMENT_64
#else
typedef struct mach_header mach_header_t;
typedef struct segment_command segment_command_t;
typedef struct section section_t;
typedef struct nlist nlist_t;
#define LC_SEGMENT_ARCH_DEPENDENT LC_SEGMENT
#endif

#ifndef SEG_DATA_CONST
#define SEG_DATA_CONST  "__DATA_CONST"
#endif

struct rebindings_entry {
    struct rebinding *rebindings;   // rebinding 数组实例
    size_t rebindings_nel;          // 元素数量
    struct rebindings_entry *next;  // 链表索引
};

// 全局量，直接拿出表头
static struct rebindings_entry *_rebindings_head;

/**
 * 将 rebinding 的多个实例组织成一个链表
 *
 * prepend_rebindings
 * struct rebindings_entry **rebindings_head
 * struct rebinding rebindings[]
 * size_t nel
 */
static int prepend_rebindings(struct rebindings_entry **rebindings_head,
                              struct rebinding rebindings[],
                              size_t nel) {
    struct rebindings_entry *new_entry = (struct rebindings_entry *) malloc(sizeof(struct rebindings_entry));
    if (!new_entry) {
        return -1;
    }
    new_entry->rebindings = (struct rebinding *) malloc(sizeof(struct rebinding) * nel);
    if (!new_entry->rebindings) {
        free(new_entry);
        return -1;
    }
    memcpy(new_entry->rebindings, rebindings, sizeof(struct rebinding) * nel);
    new_entry->rebindings_nel = nel;
    new_entry->next = *rebindings_head; // 为 new_entry->next 赋值，维护链表结构
    *rebindings_head = new_entry;       // 移动 head 指针，指向表头
    return 0;
}
// 获取进程中特定内存地址的内存保护信息，确保内存可读
static vm_prot_t get_protection(void *sectionStart) {
    mach_port_t task = mach_task_self();            // 获得任务的端口
    vm_size_t size = 0;
    vm_address_t address = (vm_address_t)sectionStart;
    memory_object_name_t object;
#if __LP64__
    mach_msg_type_number_t count = VM_REGION_BASIC_INFO_COUNT_64;
    vm_region_basic_info_data_64_t info;
    kern_return_t info_ret = vm_region_64(
                                          task, &address, &size, VM_REGION_BASIC_INFO_64, (vm_region_info_64_t)&info, &count, &object);
#else
    mach_msg_type_number_t count = VM_REGION_BASIC_INFO_COUNT;
    vm_region_basic_info_data_t info;
    kern_return_t info_ret = vm_region(task, &address, &size, VM_REGION_BASIC_INFO, (vm_region_info_t)&info, &count, &object);
#endif
    if (info_ret == KERN_SUCCESS) {
        return info.protection;
    } else {
        return VM_PROT_READ;            // 只读权限
    }
}
static void perform_rebinding_with_section(struct rebindings_entry *rebindings,
                                           section_t *section,          // _DATA.__nl_symbol_ptr（_DATA.__la_symbol_ptr）
                                           intptr_t slide,              // ASLR
                                           nlist_t *symtab,             // 符号表
                                           char *strtab,                // 字符表
                                           uint32_t *indirect_symtab)   // 间接符号表（每个条目的内容为其在 Symbol Table 中的序号）
{
    const bool isDataConst = strcmp(section->segname, SEG_DATA_CONST) == 0;         // section 是否可写
    
    uint32_t *indirect_symbol_indices = indirect_symtab + section->reserved1;       // section->reserved1 为 Section 在间接符号表中的起始条目
    void **indirect_symbol_bindings = (void **)((uintptr_t)slide + section->addr);  // 存放绑定的各个符号（section 对应的符号存在这）
    
    vm_prot_t oldProtection = VM_PROT_READ;
    if (isDataConst) {
        oldProtection = get_protection(rebindings);
        mprotect(indirect_symbol_bindings, section->size, PROT_READ | PROT_WRITE);  // 修改 indirect_symbol_bindings 为可读写权限
    }
    // 用（size / 一阶指针）来计算个数，遍历整个 Section
    for (uint i = 0; i < section->size / sizeof(void *); i++) {
        uint32_t symtab_index = indirect_symbol_indices[i];                 // 获取第 i 个地址在符号表中的序号（即，Section 的第 i 个地址对应的符号表序号）
        if (symtab_index == INDIRECT_SYMBOL_ABS ||
            symtab_index == INDIRECT_SYMBOL_LOCAL ||
            symtab_index == (INDIRECT_SYMBOL_LOCAL | INDIRECT_SYMBOL_ABS)) {
            continue;
        }
        uint32_t strtab_offset = symtab[symtab_index].n_un.n_strx;          // 在符号表中获取符号名在字符表中的偏移
        char *symbol_name = strtab + strtab_offset;                         // 获取字符表中的符号名
        bool symbol_name_longer_than_1 = symbol_name[0] && symbol_name[1];
        
        // 遍历 rebindings，依次匹配符号名
        struct rebindings_entry *cur = rebindings;
        while (cur) {
            for (uint j = 0; j < cur->rebindings_nel; j++) {
                if (symbol_name_longer_than_1 && strcmp(&symbol_name[1], cur->rebindings[j].name) == 0) {
                    // 如果是第一次对跳转地址进行重写
                    if (cur->rebindings[j].replaced != NULL && indirect_symbol_bindings[i] != cur->rebindings[j].replacement) {
                        *(cur->rebindings[j].replaced) = indirect_symbol_bindings[i];   // 记录原始跳转地址
                    }
                    indirect_symbol_bindings[i] = cur->rebindings[j].replacement;       // 重写跳转地址
                    goto symbol_loop;                                                   // 迭代到下一个
                }
            }
            cur = cur->next;
        }
    symbol_loop:;
    }
    if (isDataConst) {
        int protection = 0;
        if (oldProtection & VM_PROT_READ) {
            protection |= PROT_READ;
        }
        if (oldProtection & VM_PROT_WRITE) {
            protection |= PROT_WRITE;
        }
        if (oldProtection & VM_PROT_EXECUTE) {
            protection |= PROT_EXEC;
        }
        mprotect(indirect_symbol_bindings, section->size, protection);  // 重置权限
    }
}

static void rebind_symbols_for_image(struct rebindings_entry *rebindings,
                                     const struct mach_header *header,
                                     intptr_t slide) {
    Dl_info info;
    if (dladdr(header, &info) == 0) {
        return;
    }
    segment_command_t *cur_seg_cmd;
    segment_command_t *linkedit_segment = NULL;
    struct symtab_command* symtab_cmd = NULL;
    struct dysymtab_command* dysymtab_cmd = NULL;
    uintptr_t cur = (uintptr_t)header + sizeof(mach_header_t);      // 跳过 Mach-O Header
    // 遍历每一个 Load Command，得到 SEG_LINKEDIT、LC_SYMTAB、LC_DYSYMTAB
    for (uint i = 0; i < header->ncmds; i++, cur += cur_seg_cmd->cmdsize) {
        cur_seg_cmd = (segment_command_t *)cur;                     // 取出当前的 Load Command
        if (cur_seg_cmd->cmd == LC_SEGMENT_ARCH_DEPENDENT) {
            if (strcmp(cur_seg_cmd->segname, SEG_LINKEDIT) == 0) {  // SEG_LINKEDIT：加载命令信息
                linkedit_segment = cur_seg_cmd;
            }
        } else if (cur_seg_cmd->cmd == LC_SYMTAB) {                 // LC_SYMTAB：链接器信息
            symtab_cmd = (struct symtab_command*)cur_seg_cmd;
        } else if (cur_seg_cmd->cmd == LC_DYSYMTAB) {               // LC_DYSYMTAB：动态链接器信息
            dysymtab_cmd = (struct dysymtab_command*)cur_seg_cmd;
        }
    }
    
    if (!symtab_cmd || !dysymtab_cmd || !linkedit_segment ||
        !dysymtab_cmd->nindirectsyms) {
        return;
    }
    
    /*
        slide: ASLR 偏移量
        vmaddr: SEG_LINKEDIT 的虚拟地址
        fileoff: SEG_LINKEDIT 地址偏移
        虚拟地址偏移量 = 虚拟地址（vmaddr） - 地址移量（fileoff）
        段基址 = ASLR的偏移量（slide） + 虚拟地址偏移量
     */
    
    // Find base symbol/string table addresses
    uintptr_t linkedit_base = (uintptr_t)slide + linkedit_segment->vmaddr - linkedit_segment->fileoff;
    // 计算 symbol table 表的首地址
    nlist_t *symtab = (nlist_t *)(linkedit_base + symtab_cmd->symoff);
    // 计算 string table 首地址
    char *strtab = (char *)(linkedit_base + symtab_cmd->stroff);
    
    // 计算 indirect symbol table 的首地址
    // Get indirect symbol table (array of uint32_t indices into symbol table)
    uint32_t *indirect_symtab = (uint32_t *)(linkedit_base + dysymtab_cmd->indirectsymoff);
    
    // 遍历 Load Commands 中的 Segment Command
    cur = (uintptr_t)header + sizeof(mach_header_t);
    for (uint i = 0; i < header->ncmds; i++, cur += cur_seg_cmd->cmdsize) {
        cur_seg_cmd = (segment_command_t *)cur;                     // 取出当前的 Load Command
        if (cur_seg_cmd->cmd == LC_SEGMENT_ARCH_DEPENDENT) {        // LC_SEGMENT_64
            if (strcmp(cur_seg_cmd->segname, SEG_DATA) != 0 && strcmp(cur_seg_cmd->segname, SEG_DATA_CONST) != 0) {
                continue;                                           // 过滤 __DATA 或者 __DATA_CONST
            }
            // 遍历 Segment command 中的 Section
            for (uint j = 0; j < cur_seg_cmd->nsects; j++) {
                section_t *sect = (section_t *)(cur + sizeof(segment_command_t)) + j;
                uint32_t section_type = sect->flags & SECTION_TYPE; // 获取记录类型
                // 如果为加载符号或非懒加载符号，进行重绑定
                if (section_type == S_LAZY_SYMBOL_POINTERS || section_type == S_NON_LAZY_SYMBOL_POINTERS) {
                    perform_rebinding_with_section(rebindings, sect, slide, symtab, strtab, indirect_symtab);
                }
            }
        }
    }
}

static void _rebind_symbols_for_image(const struct mach_header *header,
                                      intptr_t slide) {
    rebind_symbols_for_image(_rebindings_head, header, slide);
}

int rebind_symbols_image(void *header,
                         intptr_t slide,
                         struct rebinding rebindings[],
                         size_t rebindings_nel) {
    struct rebindings_entry *rebindings_head = NULL;
    int retval = prepend_rebindings(&rebindings_head, rebindings, rebindings_nel);
    rebind_symbols_for_image(rebindings_head, (const struct mach_header *) header, slide);
    if (rebindings_head) {
        free(rebindings_head->rebindings);
    }
    free(rebindings_head);
    return retval;
}

int rebind_symbols(struct rebinding rebindings[], size_t rebindings_nel) {
    int retval = prepend_rebindings(&_rebindings_head, rebindings, rebindings_nel);
    if (retval < 0) {
        return retval;
    }
    if (!_rebindings_head->next) {          // NULL == _rebindings_head->next 代表第一次调用
        // 第一次调用，注册 _rebind_symbols_for_image 回调，当 dyld 链接符号时，调用此回调函数
        _dyld_register_func_for_add_image(_rebind_symbols_for_image);   // 已经加载了某些镜像，会分别对这些加载完毕的镜像调用注册的回调
    } else {
        uint32_t c = _dyld_image_count();       // 先获取 dyld 镜像数量
        for (uint32_t i = 0; i < c; i++) {      // 根据下标依次进行重绑定过程，参数 Mach-O 头，ASLR偏移量
            _rebind_symbols_for_image(_dyld_get_image_header(i), _dyld_get_image_vmaddr_slide(i));
        }
    }
    return retval;
}
