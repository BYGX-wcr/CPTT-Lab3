#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <string.h>
#include <assert.h>
#include <stdarg.h>
#include <stdbool.h>
#include "ircode.h"

/* Definitions of global data structure */

static struct CodeListItem ir_head = { NULL, OT_FLAG, NULL, NULL, NULL, NULL, NULL }; //The head Node of intermediate code list
static unsigned length = 0; //Length of ir code list led by ir_head

/* Assistant tool functions in local file */

//make a deep copy of arg:src to arg:dst
void copy_str(char** dst, const char* src) {
    *dst = malloc(strlen(src) + 1);
    strcpy(*dst, src);
}

//clear the heap space occupied by arg:target's members
void clear_item(struct CodeListItem* target) {
    free(target->left);
    free(target->right);
    free(target->dst);
    free(target->extra);

    target->left = NULL;
    target->right = NULL;
    target->dst = NULL;
    target->extra = NULL;
}

/* Operations on intermediate code list */

//add a new item to ir code list
//return the pointer of the new item
struct CodeListItem* add_code(enum OPERATOR_TYPE opt, char* left, char* right, char* dst, char* extra) {
    struct CodeListItem* new_item = malloc(CODE_LIST_ITEM_SIZE);
    memset(new_item, 0, CODE_LIST_ITEM_SIZE);

    //use arguments to fill in the new item
    new_item->opt = opt;
    if (dst != NULL) copy_str(&new_item->dst, dst);
    if (left != NULL) copy_str(&new_item->left, left);
    if (right != NULL) copy_str(&new_item->right, right);
    if (extra != NULL) copy_str(&new_item->extra, extra);

    if (length == 0) {
        ir_head.next = new_item;
        ir_head.last = new_item;
        new_item->next = &ir_head;
        new_item->last = &ir_head;
    }
    else {
        struct CodeListItem* old_tail = ir_head.last;
        old_tail->next = new_item;
        ir_head.last = new_item;
        new_item->next = &ir_head;
        new_item->last = old_tail;
    }

    length++;
    return new_item;
}

//find the item that arg:target points to and remove it
//return the pointer of next item if the operation is done, otherwise return NULL
struct CodeListItem* rm_code(struct CodeListItem* target) {
    if (length == 0 || target == NULL) return NULL;

    struct CodeListItem* ptr = ir_head.next;
    while (ptr->opt != OT_FLAG) {
        if (ptr == target) {
            struct CodeListItem* last = ptr->last;
            struct CodeListItem* next = ptr->next;
            last->next = next;
            next->last = last;

            clear_item(target);
            free(target);
            length--;
            return next;
        }
        ptr = ptr->next;
    }

    return NULL;
}

//find the item that arg:target points to and replace it
//return the pointer of replaced item if the operation is done, otherwise return NULL
struct CodeListItem* replace_code(struct CodeListItem* target, enum OPERATOR_TYPE opt, char* left, char* right, char* dst, char* extra) {
    if (length == 0 || target == NULL) return NULL;

    clear_item(target);
    target->opt = opt;
    if (dst != NULL) copy_str(&target->dst, dst);
    if (left != NULL) copy_str(&target->left, left);
    if (right != NULL) copy_str(&target->right, right);
    if (extra != NULL) copy_str(&target->extra, extra);

    return target;
}

//get the last item of arg:target
//return NULL if arg:target is NULL or the last item is the ir_head
struct CodeListItem* last_code(struct CodeListItem* target) {
    if (target == NULL || target->last->opt == OT_FLAG) {
        return NULL;
    }
    else {
        return target->last;
    }
}

//get the next item of arg:target
//return NULL if arg:target is NULL or the next item is the ir_head
struct CodeListItem* next_code(struct CodeListItem* target) {
    if (target == NULL || target->next->opt == OT_FLAG) {
        return NULL;
    }
    else {
        return target->next;
    }
}

//get the final item of ir code list
//return NULL if length = 0, otherwise return the ptr of final item
struct CodeListItem* end_code() {
    if (length == 0) return NULL;

    return ir_head.last;
}

//export the ir code list to file denoted by arg:output
void export_code( FILE* output) {
    if (length == 0) return;

    struct CodeListItem* ptr = ir_head.next;
    while (ptr->opt != OT_FLAG) {
        
        switch (ptr->opt)
        {
            case OT_LABEL: {
                fprintf(output, "LABEL %s : \n", ptr->left);
                break;
            }
            case OT_FUNC: {
                fprintf(output, "FUNCTION %s : \n", ptr->left);
                break;
            }
            case OT_ASSIGN: {
                fprintf(output, "%s := %s \n", ptr->left, ptr->right);
                break;
            }
            case OT_ADD: {
                fprintf(output, "%s := %s + %s \n", ptr->dst, ptr->left, ptr->right);
                break;
            }
            case OT_SUB: {
                fprintf(output, "%s := %s - %s \n", ptr->dst, ptr->left, ptr->right);
                break;
            }
            case OT_MUL: {
                fprintf(output, "%s := %s * %s \n", ptr->dst, ptr->left, ptr->right);
                break;
            }
            case OT_DIV: {
                fprintf(output, "%s := %s / %s \n", ptr->dst, ptr->left, ptr->right);
                break;
            }
            case OT_GOTO: {
                fprintf(output, "GOTO %s \n", ptr->left);
                break;
            }
            case OT_RELOP: {
                fprintf(output, "IF %s %s %s GOTO %s \n", ptr->left, ptr->extra, ptr->right, ptr->dst);
                break;
            }
            case OT_RET: {
                fprintf(output, "RETURN %s \n", ptr->left);
                break;
            }
            case OT_DEC: {
                fprintf(output, "DEC %s %s \n", ptr->left, ptr->right);
                break;
            }
            case OT_ARG: {
                fprintf(output, "ARG %s \n", ptr->left);
                break;
            }
            case OT_CALL: {
                fprintf(output, "%s := CALL %s \n", ptr->left, ptr->right);
                break;
            }
            case OT_PARAM: {
                fprintf(output, "PARAM %s \n", ptr->left);
                break;
            }
            case OT_READ: {
                fprintf(output, "READ %s \n", ptr->left);
                break;
            }
            case OT_WRITE: {
                fprintf(output, "WRITE %s \n", ptr->left);
                break;
            }
            default:
                assert(0);
                break;
        }

        ptr = ptr->next;
    }
}