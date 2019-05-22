#include "sparse.h"

#define ARGNUM 20

extern struct SymbolTableItem* symbol_table[TABLE_SIZE]; //a hash table

unsigned int var_count = 1;
unsigned int tmp_count = 1;
unsigned int label_count = 1;

const char ZERO[10] = "#0";
const char ONE[10] = "#1";
const char READ[10] = "READ";
const char WRITE[10] = "WRITE";
const char CALL[10] = "CALL";
const char ARG[10] = "ARG";
const char RETURN[10] = "RETURN";
const char DEC[10] = "DEC";
const char LABEL[10] = "LABEL";
const char IF[10] = "IF";
const char GOTO[10] = "GOTO";

static struct Symbol *paralist[ARGNUM];

static char *structlist[ARGNUM];
int struct_label = 0;

enum InterCodeKind { ASSIGN, ADD, SUB, MUL, STAR };
enum OperandKind { VARIABLE, CONSTANT, ADDRESS };
struct Operand {
    enum OperandKind kind;
};
struct InterCode {
    enum InterCodeKind kind;
    union {
        struct { struct Operand right, left; }assign;
        struct { struct Operand result, opl, opr; }binop;
    }code;
};
struct InterCodes {
    struct InterCode codes;
    struct InterCodes *next, *prev;
};

/* functions */
int space_create(struct Type *t);
void int_to_char(int num, char* dst); 
char *new_var(char *name);
char *new_tmp();
char *new_label();
char *new_num(char *src);
int get_offset(struct FieldList *p, char *name);
int offset_structure(char *name); 
bool in_paralist(char *name);
int use_addr(struct Node *vertex);


/* translate function declaration */

void translate_semantic(struct Node *root);
void translate_init();
void translate_visit(struct Node *vertex);
void translate_ExtDef(struct Node *vertex);
void translate_FunDec(struct Node *vertex);
void translate_CompSt(struct Node *vertex);
void translate_Def(struct Node *vertex);
void translate_DefList(struct Node *vertex);
void translate_Dec(struct Node *vertex);
void translate_DecList(struct Node *vertex);
void translate_Stmt(struct Node *vertex);
void translate_StmtList(struct Node *vertex);
void translate_VarList(struct Node *vertex);
void translate_ParamDec(struct Node *vertex);
void translate_Exp(struct Node *vertex, char *place);
void translate_Args(struct Node *vertex, char *a[], int type[], int *k);
void translate_VarDec(struct Node *vertex);
void get_structure_offset(struct Node *vertex);
void translate_Cond(struct Node *vertex, char *label_true, char *label_false);
/* function defination */

void translate_semantic(struct Node *root) {

    SAFE_ID(root, "Program");

    translate_init();

    translate_visit(root);

    // struct Symbol *p = search_symbol("mmmm");
    // if(p != NULL) {
    //     printf("exists !!\n");
    
    // Cannot translate: Code contains variables of multi-dimensional array type or
    //parameters of array type.
    
}
void translate_init() {
    memset(structlist, 0, sizeof(structlist));
}

void translate_visit(struct Node *vertex) { 
    if (CHECK_ID(vertex, "ExtDef")) {   
        translate_ExtDef(vertex);
    }
    else {
        int ptr = 0;
        while (ptr < MAX_CHILDS && vertex->childs[ptr] != NULL) {
            translate_visit(vertex->childs[ptr]);
            ptr ++;
        }
    }
}

void translate_ExtDef(struct Node *vertex) {     
    printf("%s\n",vertex->info);   
    SAFE_ID(vertex, "ExtDef");

    if (CHECK_ID(vertex->childs[1], "FunDec") && 
        (CHECK_ID(vertex->childs[2], "CompSt"))) {  
        translate_FunDec(vertex->childs[1]);
        translate_CompSt(vertex->childs[2]);
    }
}

void translate_FunDec(struct Node *vertex) {
    SAFE_ID(vertex, "FunDec");
    printf("FUNCTION %s :\n",vertex->childs[0]->info);

    memset(paralist, 0, sizeof(paralist)); // initialize paralist when each function begins

    if(CHECK_ID(vertex->childs[2], "VarList")) {
        translate_VarList(vertex->childs[2]);
    }
}

void translate_VarList(struct Node *vertex) {   
    SAFE_ID(vertex, "VarList");
    translate_ParamDec(vertex->childs[0]);
    if(vertex->childs[2] != NULL) {
        translate_VarList(vertex->childs[2]);
    }
}

void translate_ParamDec(struct Node *vertex) {
    SAFE_ID(vertex, "ParamDec");
    // printf("%s paramdec \n", vertex->childs[1]->childs[0]->info);
    SAFE_ID(vertex->childs[1], "VarDec");
    if(CHECK_ID(vertex->childs[1]->childs[0], "ID")) { // ID 
        char *dst = new_var(vertex->childs[1]->childs[0]->info);
        printf("PARAM %s \n",dst);
        struct Symbol *p = search_symbol(vertex->childs[1]->childs[0]->info);
        if(p->type->kind == STRUCTURE) {    // store structure for using v2　directly instead of &v2
            int i = 0;
            for(;i < ARGNUM && paralist[i] != NULL;i++);
            if(i < ARGNUM) {
                paralist[i] = p;
            }
        }
        else if(p->type->kind == ARRAY) {
            panic("not for us !!\n");
        }

    }
    else {
        panic("paradec is array !!! not for us !!");
    }
}

void translate_CompSt(struct Node *vertex) {
    SAFE_ID(vertex, "CompSt");
    translate_DefList(vertex->childs[1]);
    translate_StmtList(vertex->childs[2]);
}

void translate_Def(struct Node *vertex) {
    SAFE_ID(vertex, "Def");
    translate_DecList(vertex->childs[1]);
}

void translate_DefList(struct Node *vertex) {
    SAFE_ID(vertex, "DefList");
    if(CHECK_ID(vertex->childs[0], "Def")) {
        translate_Def(vertex->childs[0]);
        translate_DefList(vertex->childs[1]);
    }
}

void translate_DecList(struct Node *vertex) {
    SAFE_ID(vertex, "DecList");
    translate_Dec(vertex->childs[0]);
    if(CHECK_ID(vertex->childs[1], "COMMA")) {
        translate_DecList(vertex->childs[2]);
    }
}

void translate_Dec(struct Node *vertex) {
    SAFE_ID(vertex, "Dec");  
    if(CHECK_ID(vertex->childs[1], "ASSIGNOP")) {

        translate_VarDec(vertex->childs[0]);    // malloc space for array and structure

        if(CHECK_ID(vertex->childs[0]->childs[0], "ID")) {
            char *dst = new_var(vertex->childs[0]->childs[0]->info);
            char *src = new_tmp();
            translate_Exp(vertex->childs[2],src);
            int type = use_addr(vertex->childs[2]);
            if(type == ARRAY || type == STRUCTURE) {    
                printf("%s := *%s \n", dst, src);
            }
            else {
                printf("%s := %s \n", dst, src); 
            }
        }
        else {
            panic("not allow array or structure initialized when defined !!");
        }
    }
    else {
        translate_VarDec(vertex->childs[0]);
    }
}

void translate_VarDec(struct Node *vertex) {
    SAFE_ID(vertex, "VarDec");
    if(CHECK_ID(vertex->childs[0], "ID")) {
        struct Symbol *p = search_symbol(vertex->childs[0]->info);
        if(p->kind == VAR) {
            struct Type *t = p->type;
            int space = space_create(t);            // dec space for array and structure
            if(t->kind == ARRAY || t->kind == STRUCTURE) {
                int space = space_create(t);
                char *src = new_var(vertex->childs[0]->info);
                printf("%s %s %d \n", DEC, src, space);
            }        
        }
    }
    else {
        translate_VarDec(vertex->childs[0]);
    }
}

void translate_StmtList(struct Node *vertex) {
    SAFE_ID(vertex, "StmtList");
    if(vertex->childs[0] != NULL) {
        translate_Stmt(vertex->childs[0]);
        translate_StmtList(vertex->childs[1]);
    }
}

void translate_Stmt(struct Node *vertex) {
    SAFE_ID(vertex, "Stmt");
    if (CHECK_ID(vertex->childs[0], "RETURN")) {
        char *src = new_tmp();
        translate_Exp(vertex->childs[1], src);
        int type = use_addr(vertex->childs[1]);
        if(type == VAR) {
            printf("%s %s \n", RETURN, src);
        }
        else {
            printf("%s *%s \n", RETURN, src);
        }
    }
    else if (CHECK_ID(vertex->childs[0], "CompSt")) {
        translate_CompSt(vertex->childs[0]);
    }
    else if (CHECK_ID(vertex->childs[2], "Exp")) { 
        if(CHECK_ID(vertex->childs[0], "IF") && !CHECK_ID(vertex->childs[6], "Stmt")) { // if
            char *label_true = new_label();
            char *label_false = new_label();
            translate_Cond(vertex->childs[2], label_true, label_false); // code1
            printf("%s %s :\n", LABEL, label_true);
            translate_Stmt(vertex->childs[4]); // code2
            printf("%s %s :\n", LABEL, label_false);
        }
        else if (CHECK_ID(vertex->childs[0], "IF") && CHECK_ID(vertex->childs[6], "Stmt")) { // if else
                char *label_a = new_label();
                char *label_b = new_label();
                char *label_c = new_label();
                translate_Cond(vertex->childs[2], label_a, label_b);
                printf("%s %s :\n", LABEL, label_a);
                translate_Stmt(vertex->childs[4]);
                printf("%s %s \n", GOTO, label_c);
                printf("%s %s :\n", LABEL, label_b);
                translate_Stmt(vertex->childs[6]);
                printf("%s %s :\n", LABEL, label_c);
        }
        else { // while
            char *label_a = new_label();
            char *label_b = new_label();
            char *label_c = new_label();
            printf("%s %s :\n", LABEL, label_a);
            translate_Cond(vertex->childs[2], label_b, label_c);
            printf("%s %s :\n", LABEL, label_b);
            translate_Stmt(vertex->childs[4]);
            printf("%s %s \n", GOTO, label_a);
            printf("%s %s :\n", LABEL, label_c);
        }
            
    }
    else { // Exp SEMI
        translate_Exp(vertex->childs[0],NULL);
    }
}

void translate_Exp(struct Node* vertex, char *place) {
    SAFE_ID(vertex, "Exp");

    if (CHECK_ID(vertex->childs[0], "ID") && !CHECK_ID(vertex->childs[1], "LP")) { //Var reference
        if(place == NULL) return;
        struct ExpType p = Exp(vertex);
        int type = p.type->kind;
        if(type == VAR) {
            char *src = new_var(vertex->childs[0]->info);
            printf("%s := %s \n", place, src);
        }
        else {  
            bool flag = in_paralist(vertex->childs[0]->info);
            struct Symbol *p = search_symbol(vertex->childs[0]->info);
            char *v1 = new_var(vertex->childs[0]->info);
            if(flag) {
                printf("%s := %s \n", place, v1);
            }
            else {
                printf("%s := &%s \n", place, v1);
            }
        }
    }
    else if (CHECK_ID(vertex->childs[0], "INT")) {
        if(place == NULL) return;
        char *tmp = new_num(vertex->childs[0]->info);
        printf("%s := %s \n", place, tmp);
    }
    else if (CHECK_ID(vertex->childs[0], "FLOAT")) {
        if(place == NULL) return;
        printf("%s := %s \n", place,vertex->childs[0]->info);

    }
    else if (CHECK_ID(vertex->childs[1], "ASSIGNOP")) {     
        char *src = new_tmp();
        char *dst = new_tmp();
        int left = use_addr(vertex->childs[0]);
        int right = use_addr(vertex->childs[2]);
        // printf("%d , %d debug \n", left, right);
        translate_Exp(vertex->childs[2],src);
        translate_Exp(vertex->childs[0],dst);
        if(left == VAR) {
            dst = new_var(vertex->childs[0]->childs[0]->info);
            if(right == VAR) {
                printf("%s := %s \n", dst, src);               
            }
            else {
                printf("%s := *%s \n", dst, src);
            }
        }
        else {  
            if(right == VAR) {
                printf("*%s := %s \n", dst, src);
            }
            else {
                printf("*%s := *%s \n", dst, src);
            }
        }
        // if(place != NULL) {
        //     printf("%s := %s \n", place, dst);
        // }
    }
    else if (CHECK_ID(vertex->childs[1], "AND") || CHECK_ID(vertex->childs[1], "OR")
            || CHECK_ID(vertex->childs[1], "RELOP") || CHECK_ID(vertex->childs[0], "NOT")) {
        
        char *label_true = new_label();
        char *label_false = new_label();
        printf("%s := %s \n", place, ZERO);
        translate_Cond(vertex, label_true, label_false);
        printf("%s %s :\n", LABEL, label_true);
        printf("%s := %s\n", place, ONE);
        printf("%s %s :\n", LABEL, label_false);
    }
    else if (CHECK_ID(vertex->childs[1], "PLUS")) {
        if(place == NULL) return;
        int left = use_addr(vertex->childs[0]);
        int right = use_addr(vertex->childs[2]);
        char *src = new_tmp();
        char *dst = new_tmp();
        translate_Exp(vertex->childs[2], src);
        translate_Exp(vertex->childs[0], dst);
        if(left != VAR && right != VAR) {
            printf("%s := *%s + *%s \n", place, dst, src);
        }
        else if(left != VAR && right == VAR) {
            printf("%s := *%s + %s \n", place, dst, src);
        }
        else if(left == VAR && right != VAR) {
            printf("%s := %s + *%s \n", place, dst, src);
        }
        else {
            printf("%s := %s + %s \n", place, dst, src);
        }
    }
    else if(CHECK_ID(vertex->childs[1], "MINUS")) {
        if(place == NULL) return;
        char *src = new_tmp();
        char *dst = new_tmp();
        translate_Exp(vertex->childs[2], src);
        translate_Exp(vertex->childs[0], dst);
        printf("%s := %s - %s \n", place, dst, src);
    }

    else if(CHECK_ID(vertex->childs[1], "STAR")) {
        if(place == NULL) return;
        char *src = new_tmp();
        char *dst = new_tmp();
        translate_Exp(vertex->childs[2], src);
        translate_Exp(vertex->childs[0], dst);
        printf("%s := %s * %s \n", place, dst, src);
    }

    else if(CHECK_ID(vertex->childs[1], "DIV")) {
        if(place == NULL) return;
        char *src = new_tmp();
        char *dst = new_tmp();
        translate_Exp(vertex->childs[2], src);
        translate_Exp(vertex->childs[0], dst);
        printf("%s := %s / %s \n", place, dst, src);
    }
    else if (CHECK_ID(vertex->childs[0], "MINUS")) {
        if(place == NULL) return;
        char *src = new_tmp();
        translate_Exp(vertex->childs[1], src);
        printf("%s := %s - %s \n", place, ZERO, src);
    }
    else if(CHECK_ID(vertex->childs[0], "LP") && CHECK_ID(vertex->childs[1], "Exp")) {
        char *src = new_tmp();
        translate_Exp(vertex->childs[1], src);
        if(place != NULL) {
            printf("%s := %s \n", place, src);
        }
    }
    else if (CHECK_ID(vertex->childs[0], "ID") && CHECK_ID(vertex->childs[1], "LP")) { //function invoking
        if(CHECK_ID(vertex->childs[2], "Args")) { // ID LP Args RP
            char *a[ARGNUM];
            int argtype[2*ARGNUM];
            memset(a, 0, sizeof(char *)*ARGNUM);
            int len = 0;                            
            translate_Args(vertex->childs[2], a, argtype, &len);
            if(!strcmp(vertex->childs[0]->info, "write")) {
                int type = use_addr(vertex->childs[2]->childs[0]);
                if(type != VAR) {
                    char *t1 = new_tmp();
                    printf("%s := *%s\n", t1, a[0]);
                    printf("%s %s \n", WRITE, t1);
                }
                else {
                    printf("%s %s \n", WRITE, a[0]);
                }
                return;
            }
            else {
                for (int i = len - 1; i >= 0; i--) {
                    if(argtype[2*i] != VAR) {
                        printf("%s %s \n", ARG, a[i]);
                    }
                    else if(argtype[2*i] == VAR && argtype[2*i+1] != VAR) {
                        printf("%s *%s \n", ARG, a[i]);
                    }
                    else if(argtype[2*i] == VAR && argtype[2*i+1] == VAR) {
                        printf("%s %s \n", ARG, a[i]);
                    }
                    else {
                        panic("type is not illegal !!\n");
                    }
                }
                printf("%s := %s %s \n", place, CALL, vertex->childs[0]->info);
            }
        }
        else { // ID LP RP
            if (!strcmp(vertex->childs[0]->info, "read")) {
                char *src = new_tmp();
                if(place != NULL) {
                    printf("%s %s \n", READ, src);
                    printf("%s := %s \n", place, src);
                    return;
                }
            }
            else {
                if(place != NULL) {
                    printf("%s := %s %s \n", place, CALL, vertex->childs[0]->info);
                }
            }
        }
    }
    else if (CHECK_ID(vertex->childs[1], "LB")) {
        int offset = 0;
        struct Node *v = vertex->childs[0];


        char *t1 = new_tmp();
        char *t2 = new_tmp();
        int type = use_addr(vertex->childs[2]);
        if (type == VAR) {
            translate_Exp(vertex->childs[2], t1); // index
        }
        else {
            char *t3 = new_tmp();
            translate_Exp(vertex->childs[2], t3);
            printf("%s := *%s \n", t1, t3);
        }
        printf("%s := %s * #%d \n", t2, t1, 4);

        if(CHECK_ID(v->childs[0], "ID") && !CHECK_ID(v->childs[1], "LP")) {
            char *name = v->childs[0]->info;        
            char *v1 = new_var(name);
            bool flag = in_paralist(name);
            struct Symbol *p = search_symbol(name);
            if (p->kind == VAR && p->type->kind == ARRAY) {       
                if(!flag) {
                    char tmp[ARGNUM];
                    tmp[0] = '&';
                    strcpy(tmp + 1, v1);
                    strcpy(v1, tmp);
                }
                printf("%s := %s + %s \n", place, v1, t2);
            }

        }
        else if(CHECK_ID(v->childs[0], "Exp") && CHECK_ID(v->childs[1], "LB")) {
            panic("multimensional array !!!\n");
        }
        else if(CHECK_ID(v->childs[0], "Exp") && CHECK_ID(v->childs[1], "DOT")) {
            char *tmp = new_tmp();
            translate_Exp(v, tmp); // get offset
            printf("%s := %s + %s \n", place, tmp, t2);
        } 

    }
    else if (CHECK_ID(vertex->childs[1], "DOT")) {     
        get_structure_offset(vertex);
        char *first = structlist[0];
        char *v1 = new_var(first); 
        int offset = offset_structure(vertex->childs[2]->info);
        if(in_paralist(first)) {
            printf("%s := %s + #%d \n", place, v1, offset);
        }
        else {
            printf("%s := &%s + #%d \n", place, v1, offset);
        }
    }
}

void translate_Cond(struct Node *vertex, char *label_true, char *label_false) {
    if(CHECK_ID(vertex->childs[0], "Exp") && CHECK_ID(vertex->childs[1], "RELOP")){
        char *t1 = new_tmp();
        char *t2 = new_tmp();
        char *op = vertex->childs[1]->info;
        translate_Exp(vertex->childs[0], t1);
        translate_Exp(vertex->childs[2], t2);
        printf("%s %s %s %s %s %s\n", IF, t1, op, t2, GOTO, label_true);
        printf("%s %s\n", GOTO, label_false);

    }
    else if(CHECK_ID(vertex->childs[0], "NOT")) {
        translate_Cond(vertex->childs[1], label_false, label_true);
    }
    else if(CHECK_ID(vertex->childs[1], "AND")) {
        char *label_tmp = new_label();
        translate_Cond(vertex->childs[0], label_tmp, label_false);
        printf("%s %s :\n", LABEL, label_tmp);
        translate_Cond(vertex->childs[2], label_true, label_false);
    }
    else if(CHECK_ID(vertex->childs[1], "OR")) {
        char *label_tmp = new_label();
        translate_Cond(vertex->childs[0], label_true, label_tmp);
        printf("%s %s :\n", LABEL, label_tmp);
        translate_Cond(vertex->childs[2], label_true, label_false);
    }
    else {
        char *t1 = new_tmp();
        translate_Exp(vertex, t1);
        char op[10] = "!=";
        printf("%s %s %s %s %s %s \n", IF, t1, op, ZERO, GOTO, label_true);
        printf("%s %s \n", GOTO, label_false);
    }
}

void get_structure_offset(struct Node *vertex) {
        struct Node *v = vertex->childs[0];
        if(CHECK_ID(v->childs[0], "ID") && !CHECK_ID(v->childs[1], "LP")) {

            char *name = v->childs[0]->info;
            structlist[struct_label ++] = name;
            structlist[struct_label ++] = vertex->childs[2]->info;
        }
        else {  
            get_structure_offset(vertex->childs[0]);
            char *id_name = vertex->childs[2]->info;
            structlist[struct_label ++] = id_name;
        }
}
void translate_Args(struct Node *vertex, char *a[], int type[], int *k) {

    struct ExpType p = Exp(vertex->childs[0]);
    if (p.type->kind == ARRAY) {
        panic("not for us \n");
    }
    else {
        char *src = new_tmp();
        translate_Exp(vertex->childs[0], src);
        type[2*(*k)] = Exp(vertex->childs[0]).type->kind;
        type[2*(*k) + 1] = use_addr(vertex->childs[0]);
        a[*k] = src;
        *k = (*k) + 1;
    }
    if(CHECK_ID(vertex->childs[2], "Args")) {
        translate_Args(vertex->childs[2], a, type, k);
    }
}

int use_addr(struct Node *vertex) {
    if(CHECK_ID(vertex->childs[0], "Exp") && CHECK_ID(vertex->childs[1], "DOT")) {
        return STRUCTURE;
    }
    else if(CHECK_ID(vertex->childs[0], "Exp") && CHECK_ID(vertex->childs[1], "LB")) {
        return ARRAY;
    }
    return VAR;
}

bool in_paralist(char *name) {
    bool flag = false;
    int i = 0;
    while (i < ARGNUM && paralist[i] != NULL && strcmp(paralist[i]->id, name) != 0) {
        i++;
    }
    flag = (i == ARGNUM || paralist[i] == NULL) ? false : true;
    return flag;
}

int get_offset(struct FieldList *p, char *name) {
    int offset = 0;
    while (p != NULL && strcmp(name, p->id) != 0) { 
        if (p->type->kind == BASIC) {
            offset += 4;
        }
        else if (p->type->kind == ARRAY) {
            offset += p->type->array.size * 4;
        }
        else {
            struct FieldList *m = p->type->structure;
            offset += get_offset(m, name);
        }
        p = p->next;
    }
    // printf("ｇｅｔ off set %d \n", offset);
    return offset;
}

int offset_structure(char *name) {
    int offset = 0;
    // for(int i = 0;i < struct_label;i++) {
    //     printf("***** %s \n", structlist[i]);
    // }
    struct FieldList *p = search_symbol(structlist[0])->type->structure;
    struct FieldList *q = p;
    for(int i = 0;i < struct_label - 2;i++) {
        char *tmp = structlist[i+1];        
        offset += get_offset(p, tmp);
        while(q != NULL && strcmp(q->id, tmp) != 0) {
            q = q->next;
        }
        p = q->type->structure;
        q = p;
    }
    offset += get_offset(p, name);
    memset(structlist, 0, sizeof(structlist));          // initialized to zero
    struct_label = 0;
    return offset;
}

int space_create(struct Type *t) {
    if(t->kind == BASIC) {
        return 4;
    }
    else if(t->kind == ARRAY) {
        return t->array.size * space_create(t->array.elem_type);
    }
    else {  // structure
        int space = 0;
        for(struct FieldList *p = t->structure;p != NULL;p = p->next) {
            space += space_create(p->type);
        }
        return space;
    }
}

void int_to_char(int num, char *dst) {
    int m = num, n = 0, k = 0;
    while (m != 0)
    {
        n = m % 10;
        dst[k++] = n + '0';
        m = m / 10;
    }
    dst[k] = '\0'; 
    for(int i = 0, j = k-1;i <= j;i++, j--) {
        char tmp = dst[i];
        dst[i] = dst[j];
        dst[j] = tmp;
    }
}

char *new_var(char *name) {
    char *dst = (char *)malloc(sizeof(char)*ARGNUM);
    memset(dst, 0, sizeof(char)*strlen(dst));
    struct Symbol *p = search_symbol(name);
    if (p != NULL && (p->kind == VAR))
    {
        dst[0] = 'v';
        char src[10];
        int_to_char(p->var_num, src);
        strcpy(dst + 1, src);
    }
    else
    {
        panic("name is illegal !!\n");
    }
    return dst;
}

char *new_tmp() {   
    char *dst = (char *)malloc(sizeof(char)*ARGNUM);
    memset(dst, 0, sizeof(char)*strlen(dst));
    dst[0] = 't';
    char src[10];
    int_to_char(tmp_count++, src);
    strcpy(dst+1, src);
    return dst;
}

char *new_label() {   
    char *dst = (char *)malloc(sizeof(char)*ARGNUM);
    memset(dst, 0, sizeof(char)*strlen(dst));  
    char tmp[10] = "label";
    char src[10];
    strcpy(dst,tmp);
    int_to_char(label_count++, src);
    strcpy(dst+5, src);
    return dst;
}

char *new_num(char *src) {
    char *dst = (char *)malloc(sizeof(char)*30);
    memset(dst, 0, sizeof(char)*strlen(dst));
    dst[0] = '#';
    strcpy(dst+1, src);
    return dst;
}