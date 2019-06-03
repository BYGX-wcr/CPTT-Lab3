#include "sparse.h"
#include "ircode.h"

#define ARGNUM 20

extern struct SymbolTableItem* symbol_table[TABLE_SIZE]; //a hash table

unsigned int var_count = 1;
unsigned int tmp_count = 1;
unsigned int label_count = 1;

char ZERO[10] = "#0";
char ONE[10] = "#1";
char READ[10] = "READ";
char WRITE[10] = "WRITE";
char CALL[10] = "CALL";
char ARG[10] = "ARG";
char RETURN[10] = "RETURN";
char DEC[10] = "DEC";
char LABEL[10] = "LABEL"; 
char IF[10] = "IF";
char GOTO[10] = "GOTO";

static struct Symbol *paralist[ARGNUM]; // paramdec list

static char *structlist[ARGNUM]; // search Node struct to get offset directly
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
char *new_imm(char *src);
int part_offset(struct FieldList *p, char *name);
int total_offset(char *name); 
bool in_paralist(char *name);
int use_addr(struct Node *vertex);
bool legal_to_output();
char *num2imm(int n);
void add_ch(char *dst, char ch);

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
void get_structlist(struct Node *vertex);
void translate_Cond(struct Node *vertex, char *label_true, char *label_false);

/* function definition */

void translate_semantic(struct Node *root) {
    SAFE_ID(root, "Program");

    translate_init();

    if(legal_to_output()) {
        FILE *file = fopen("../result.ir","w");
        translate_visit(root);
        export_code(file);
        fclose(file);
    }
    else {
        printf("Cannot translate: Code contains variables of multi-dimensional array type or parameters of array type. \n");
    }    
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
    SAFE_ID(vertex, "ExtDef");

    if (CHECK_ID(vertex->childs[1], "FunDec") && 
        (CHECK_ID(vertex->childs[2], "CompSt"))) {  
        translate_FunDec(vertex->childs[1]);
        translate_CompSt(vertex->childs[2]);
    }
}

void translate_FunDec(struct Node *vertex) {
    SAFE_ID(vertex, "FunDec");
    //printf("FUNCTION %s :\n", vertex->childs[0]->info);
    add_code(OT_FUNC, vertex->childs[0]->info, NULL, NULL, NULL);
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
    SAFE_ID(vertex->childs[1], "VarDec");
    if(CHECK_ID(vertex->childs[1]->childs[0], "ID")) { // ID 
        char *dst = new_var(vertex->childs[1]->childs[0]->info);
        add_code(OT_PARAM, dst, NULL, NULL, NULL);
        struct Symbol *p = search_symbol(vertex->childs[1]->childs[0]->info);
        if(p->type->kind == STRUCTURE) {    // store structure for using v2　directly instead of &v2
            int i = 0;
            for(;i < ARGNUM && paralist[i] != NULL;i++);
            if(i < ARGNUM) {
                paralist[i] = p;
            }
        }
        else if(p->type->kind == ARRAY) {
            panic("impossible param!!\n");
        }

    }
    else {
        panic("impossible param2!!\n");
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
                //printf("%s := *%s \n", dst, src);
                add_ch(src, '*');
            }
            else {
                //printf("%s := %s \n", dst, src); 
            }
            add_code(OT_ASSIGN, dst, src, NULL, NULL);
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
            if((t->kind == ARRAY && t->array.elem_type->kind == BASIC) || t->kind == STRUCTURE) {
                int space = space_create(t);
                char *src = new_var(vertex->childs[0]->info);
                //printf("%s %s %d \n", DEC, src, space);

                char *space_char = (char *)malloc(sizeof(char)*ARGNUM);
                int_to_char(space, space_char);
                add_code(OT_DEC, src, space_char, NULL, NULL);
            }
            else if(t->kind == ARRAY && t->array.elem_type->kind != BASIC) {
                panic("impossible vardec !!\n");
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
            //printf("%s %s \n", RETURN, src);

            add_code(OT_RET, src, NULL, NULL, NULL);
        }
        else {
            //printf("%s *%s \n", RETURN, src);

            add_ch(src, '*');
            add_code(OT_RET, src, NULL, NULL, NULL);
        }
    }
    else if (CHECK_ID(vertex->childs[0], "CompSt")) {
        translate_CompSt(vertex->childs[0]);
    }
    else if (CHECK_ID(vertex->childs[2], "Exp")) { 
        if(CHECK_ID(vertex->childs[0], "IF") && !CHECK_ID(vertex->childs[6], "Stmt")) { // if
            char *label_true = new_label();
            char *label_false = new_label();
            translate_Cond(vertex->childs[2], label_true, label_false); // code of cond exp
            //printf("%s %s\n", GOTO, label_false);
            //printf("%s %s :\n", LABEL, label_true);
            add_code(OT_LABEL, label_true, NULL, NULL, NULL);
            translate_Stmt(vertex->childs[4]); // code of true
            //printf("%s %s :\n", LABEL, label_false);
            add_code(OT_LABEL, label_false, NULL, NULL, NULL);
        }
        else if (CHECK_ID(vertex->childs[0], "IF") && CHECK_ID(vertex->childs[6], "Stmt")) { // if else
                char *label_a = new_label();
                char *label_b = new_label();
                char *label_c = new_label();
                // translate_Cond(vertex->childs[2], label_a, label_b);
                // printf("%s %s :\n", LABEL, label_a);
                // add_code(OT_LABEL, label_a, NULL, NULL, NULL);
                // translate_Stmt(vertex->childs[4]);
                // printf("%s %s \n", GOTO, label_c);
                // add_code(OT_GOTO, label_c, NULL, NULL, NULL);
                // printf("%s %s :\n", LABEL, label_b);
                // add_code(OT_LABEL, label_b, NULL, NULL, NULL);
                // translate_Stmt(vertex->childs[6]);
                // printf("%s %s :\n", LABEL, label_c);
                // add_code(OT_LABEL, label_c, NULL, NULL, NULL);

                translate_Cond(vertex->childs[2], label_a, label_b); // code of cond exp
                /* optimized:reduce GOTO stmt */
                struct CodeListItem* goto_b = end_code();
                assert(rm_code(goto_b) != NULL);

                translate_Stmt(vertex->childs[6]); // code of false
                add_code(OT_GOTO, label_c, NULL, NULL, NULL);

                add_code(OT_LABEL, label_a, NULL, NULL, NULL);
                translate_Stmt(vertex->childs[4]); // code of true

                add_code(OT_LABEL, label_c, NULL, NULL, NULL);
        }
        else { // while
            char *label_a = new_label();
            char *label_b = new_label();
            char *label_c = new_label();
            add_code(OT_LABEL, label_a, NULL, NULL, NULL);
            translate_Cond(vertex->childs[2], label_b, label_c);
            add_code(OT_LABEL, label_b, NULL, NULL, NULL);
            translate_Stmt(vertex->childs[4]);
            add_code(OT_GOTO, label_a, NULL, NULL, NULL);
            add_code(OT_LABEL, label_c, NULL, NULL, NULL);
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
            memset(place, 0, sizeof(char)*ARGNUM);
            strcpy(place, src);
        }
        else {  
            bool flag = in_paralist(vertex->childs[0]->info);
            struct Symbol *p = search_symbol(vertex->childs[0]->info);
            char *v1 = new_var(vertex->childs[0]->info);
            if(flag) {
                //printf("%s := %s \n", place, v1);
            }
            else {
                //printf("%s := &%s \n", place, v1);
                add_ch(v1, '&');
            }
            //add_code(OT_ASSIGN, place, v1, NULL, NULL);
            //place = v1;

            memset(place, 0, sizeof(char)*ARGNUM);
            strcpy(place, v1);
        }
    }
    else if (CHECK_ID(vertex->childs[0], "INT") || CHECK_ID(vertex->childs[0], "FLOAT")) {
        if(place == NULL) return;
        char *tmp = new_imm(vertex->childs[0]->info);   

        memset(place, 0, sizeof(char)*ARGNUM);
        strcpy(place, tmp);
    }
    else if (CHECK_ID(vertex->childs[1], "ASSIGNOP")) {     
        char *src = new_tmp();
        char *dst = new_tmp();
        int left = use_addr(vertex->childs[0]);
        int right = use_addr(vertex->childs[2]);
        translate_Exp(vertex->childs[2], src);
        if(left == VAR) {
            translate_Exp(vertex->childs[0], dst);
            if (place != NULL && vertex->childs[0] != NULL && (CHECK_ID(vertex->childs[0]->childs[0], "ID"))) {
                //printf("cur: %s\n", place);
                //printf("target: %s\n", new_var(vertex->childs[0]->childs[0]->info));
                strcpy(place, new_var(vertex->childs[0]->childs[0]->info));
                //printf("after: %s\n", place);
            }

            if(right == VAR) {
                //printf("%s := %s \n", dst, src);              
            }
            else {
                //printf("%s := *%s \n", dst, src);
                add_ch(src, '*');
            }
        }
        else {
            translate_Exp(vertex->childs[0], dst);
            if(right == VAR) {
                //printf("*%s := %s \n", dst, src);
                add_ch(dst, '*');
            }
            else {
                //printf("*%s := *%s \n", dst, src);
                add_ch(dst, '*');
                add_ch(src, '*');
            }
        }
        add_code(OT_ASSIGN, dst, src, NULL, NULL);
        if(place != NULL && strcmp(place, dst)) {
            add_code(OT_ASSIGN, place, dst, NULL, NULL);
        }
    }
    else if (CHECK_ID(vertex->childs[1], "AND") || CHECK_ID(vertex->childs[1], "OR")
            || CHECK_ID(vertex->childs[1], "RELOP") || CHECK_ID(vertex->childs[0], "NOT")) {
        
        char *label_true = new_label();
        char *label_false = new_label();
        add_code(OT_ASSIGN, place, ZERO, NULL, NULL);
        translate_Cond(vertex, label_true, label_false);
        add_code(OT_LABEL, label_true, NULL, NULL, NULL);
        add_code(OT_ASSIGN, place, ONE, NULL, NULL);
        add_code(OT_LABEL, label_false, NULL, NULL, NULL);
    }
    else if (CHECK_ID(vertex->childs[1], "PLUS") || CHECK_ID(vertex->childs[1], "MINUS")
            || CHECK_ID(vertex->childs[1], "STAR") || CHECK_ID(vertex->childs[1], "DIV")) {
        if(place == NULL) return;
        int left = use_addr(vertex->childs[0]);
        int right = use_addr(vertex->childs[2]);
        char *src = new_tmp();
        char *dst = new_tmp();
        translate_Exp(vertex->childs[2], src);
        translate_Exp(vertex->childs[0], dst);
        char *op = vertex->childs[1]->info;
        if(left != VAR && right != VAR) {
            //printf("%s := *%s %s *%s \n", place, dst, op, src);
            add_ch(dst, '*');
            add_ch(src, '*');
        }
        else if(left != VAR && right == VAR) {
            //printf("%s := *%s %s %s \n", place, dst, op, src);
            add_ch(dst, '*');
        }
        else if(left == VAR && right != VAR) {
            //printf("%s := %s %s *%s \n", place, dst, op, src);
            add_ch(src, '*');
        }
        else {
            //printf("%s := %s %s %s \n", place, dst, op, src);
        }
        if(CHECK_ID(vertex->childs[1], "PLUS")) add_code(OT_ADD, dst, src, place, NULL);
        else if(CHECK_ID(vertex->childs[1], "MINUS")) add_code(OT_SUB, dst, src, place, NULL);
        else if(CHECK_ID(vertex->childs[1], "STAR")) add_code(OT_MUL, dst, src, place, NULL);
        else add_code(OT_DIV, dst, src, place, NULL);
    }
    else if (CHECK_ID(vertex->childs[0], "MINUS")) {
        if(place == NULL) return;
        char *src = new_tmp();
        translate_Exp(vertex->childs[1], src);
        add_code(OT_SUB, ZERO, src, place, NULL);
    }
    else if(CHECK_ID(vertex->childs[0], "LP") && CHECK_ID(vertex->childs[1], "Exp")) {
        // char *src = new_tmp();
        // translate_Exp(vertex->childs[1], src);
        // if(place != NULL) {
        //     printf("%s := %s \n", place, src);
        //     add_code(OT_ASSIGN, place, src, NULL, NULL);
        // }

        /* optimized:reduce assign operations */
        translate_Exp(vertex->childs[1], place);
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
                    char *tmp = num2imm(0);
                    strcpy(tmp, a[0]);
                    add_ch(tmp, '*');
                    add_code(OT_WRITE, tmp, NULL, NULL, NULL);
                }
                else {
                    add_code(OT_WRITE, a[0], NULL, NULL, NULL);
                }
                return;
            }
            else {
                for (int i = len - 1; i >= 0; i--) {
                    if(argtype[2*i] != VAR) {
                        add_code(OT_ARG, a[i], NULL, NULL, NULL);
                    }
                    else if(argtype[2*i] == VAR && argtype[2*i+1] != VAR) {
                        char *tmp = num2imm(0);
                        strcpy(tmp, a[i]);
                        add_ch(tmp, '*');
                        add_code(OT_ARG, tmp, NULL, NULL, NULL);
                    }
                    else if(argtype[2*i] == VAR && argtype[2*i+1] == VAR) {
                        add_code(OT_ARG, a[i], NULL, NULL, NULL);
                    }
                    else {
                        panic("type is illegal !!\n");
                    }
                }
                if(place != NULL) {
                    add_code(OT_CALL, place, vertex->childs[0]->info, NULL, NULL);
                }
                else {
                    char *t = new_tmp();
                    add_code(OT_CALL, t, vertex->childs[0]->info, NULL, NULL);
                }
            }
        }
        else { // ID LP RP
            if (!strcmp(vertex->childs[0]->info, "read")) {
                if(place != NULL) {
                    /* optimized:reduce assign operations */
                    add_code(OT_READ, place, NULL, NULL, NULL);
                    return;
                }
            }
            else {
                if(place != NULL) {
                    add_code(OT_CALL, place, vertex->childs[0]->info, NULL, NULL);
                }
                else {
                    char *t = new_tmp();
                    add_code(OT_CALL, t, vertex->childs[0]->info, NULL, NULL);
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
            add_ch(t3, '*');
            add_code(OT_ASSIGN, t1, t3, NULL, NULL);
        }
        char *num = num2imm(4);
        add_code(OT_MUL, t1, num, t2, NULL);

        if(CHECK_ID(v->childs[0], "ID") && !CHECK_ID(v->childs[1], "LP")) {
            char *name = v->childs[0]->info;        
            char *v1 = new_var(name);
            bool flag = in_paralist(name);
            struct Symbol *p = search_symbol(name);
            if (p->kind == VAR && p->type->kind == ARRAY) {       
                if(!flag) {
                    add_ch(v1, '&');
                }
                add_code(OT_ADD, v1, t2, place, NULL);
            }

        }
        else if(CHECK_ID(v->childs[0], "Exp") && CHECK_ID(v->childs[1], "LB")) {
            panic("multimensional array !!!\n");
        }
        else if(CHECK_ID(v->childs[0], "Exp") && CHECK_ID(v->childs[1], "DOT")) {
            char *tmp = new_tmp();
            translate_Exp(v, tmp); // get offset
            add_code(OT_ADD, tmp, t2, place, NULL);
        } 

    }
    else if (CHECK_ID(vertex->childs[1], "DOT")) {     
        get_structlist(vertex);
        char *first = structlist[0];
        char *v1 = new_var(first); 
        int offset = total_offset(vertex->childs[2]->info);         // get offset
        char *num = num2imm(offset);
      
        if(in_paralist(first)) {
            add_code(OT_ADD, v1, num, place, NULL);
        }
        else {
            add_ch(v1, '&');
            add_code(OT_ADD, v1, num, place, NULL);
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
        if(use_addr(vertex->childs[0])) {           // element in array or structure
            add_ch(t1, '*');
        }
        if(use_addr(vertex->childs[2])) {
            add_ch(t2, '*');
        }
        add_code(OT_RELOP, t1, t2, label_true, op);
        add_code(OT_GOTO, label_false, NULL, NULL, NULL);

    }
    else if(CHECK_ID(vertex->childs[0], "NOT")) {
        translate_Cond(vertex->childs[1], label_false, label_true);
    }
    else if(CHECK_ID(vertex->childs[1], "AND")) {
        char *label_tmp = new_label();
        translate_Cond(vertex->childs[0], label_tmp, label_false);
        add_code(OT_LABEL, label_tmp, NULL, NULL, NULL);
        translate_Cond(vertex->childs[2], label_true, label_false);
    }
    else if(CHECK_ID(vertex->childs[1], "OR")) {
        char *label_tmp = new_label();
        translate_Cond(vertex->childs[0], label_true, label_tmp);
        add_code(OT_LABEL, label_tmp, NULL, NULL, NULL);
        translate_Cond(vertex->childs[2], label_true, label_false);
    }
    else {
        char *t1 = new_tmp();
        translate_Exp(vertex, t1);
        if(use_addr(vertex)) {
            add_ch(t1, '*');
        }
        char op[10] = "!=";
        add_code(OT_RELOP, t1, ZERO, label_true, op);
        add_code(OT_GOTO, label_false, NULL, NULL, NULL);
    }
}

void get_structlist(struct Node *vertex) {
        struct Node *v = vertex->childs[0];
        if(CHECK_ID(v->childs[0], "ID") && !CHECK_ID(v->childs[1], "LP")) {

            char *name = v->childs[0]->info;
            structlist[struct_label ++] = name;
            structlist[struct_label ++] = vertex->childs[2]->info;
        }
        else {  
            get_structlist(vertex->childs[0]);
            char *id_name = vertex->childs[2]->info;
            structlist[struct_label ++] = id_name;
        }
}
void translate_Args(struct Node *vertex, char *a[], int type[], int *k) {

    struct ExpType p = Exp(vertex->childs[0]);
    if (p.type->kind == ARRAY) {
        panic("impossible !!\n");
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
    if (CHECK_ID(vertex->childs[0], "LP")) {
        return use_addr(vertex->childs[1]);
    }
    if (CHECK_ID(vertex->childs[0], "Exp") && CHECK_ID(vertex->childs[1], "DOT")) {
        return STRUCTURE;
    }
    else if (CHECK_ID(vertex->childs[0], "Exp") && CHECK_ID(vertex->childs[1], "LB")) {
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

int part_offset(struct FieldList *p, char *name) {
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
            offset += part_offset(m, name);
        }
        p = p->next;
    }
    return offset;
}

int total_offset(char *name) {
    int offset = 0;
    struct FieldList *p = search_symbol(structlist[0])->type->structure;
    struct FieldList *q = p;
    for(int i = 0;i < struct_label - 2;i++) {
        char *tmp = structlist[i+1];        
        offset += part_offset(p, tmp);
        while(q != NULL && strcmp(q->id, tmp) != 0) {
            q = q->next;
        }
        p = q->type->structure;
        q = p;
    }
    offset += part_offset(p, name);
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
    do
    {
        n = m % 10;
        dst[k++] = n + '0';
        m = m / 10;
    } while (m != 0);
    dst[k] = '\0';

    for(int i = 0, j = k-1; i <= j; i++, j--) {
        char tmp = dst[i];
        dst[i] = dst[j];
        dst[j] = tmp;
    }
}

char *num2imm(int n) {
    char *dst = (char *)malloc(sizeof(char)*ARGNUM);
    char src[ARGNUM];
    int_to_char(n, src);
    dst[0] = '#';
    strcpy(dst+1, src);
    return dst;
}

void add_ch(char *dst, char ch) {
    char src[ARGNUM];
    strcpy(src, dst);
    memset(dst, 0, strlen(dst));
    dst[0] = ch;
    strncpy(dst + 1, src, strlen(src));
}

char *new_var(char *name) {
    char *dst = (char *)malloc(sizeof(char)*ARGNUM);
    memset(dst, 0, sizeof(char)*ARGNUM);
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
    memset(dst, 0, sizeof(char)*ARGNUM);
    dst[0] = 't';
    char src[10];
    int_to_char(tmp_count++, src);
    strcpy(dst + 1, src);
    return dst;
}

char *new_label() {   
    char *dst = (char *)malloc(sizeof(char)*ARGNUM);
    memset(dst, 0, sizeof(char)*ARGNUM);  
    char tmp[10] = "label";
    char src[10];
    strcpy(dst,tmp);
    int_to_char(label_count++, src);
    strcpy(dst + 5, src);
    return dst;
}

char *new_imm(char *src) {
    char *dst = (char *)malloc(sizeof(char)*ARGNUM);
    memset(dst, 0, sizeof(char)*ARGNUM);
    dst[0] = '#';
    strcpy(dst + 1, src);
    return dst;
}

bool structure_arrays(struct FieldList *s) {
    bool flag = true;
    while (s != NULL) {
        if(s->type->kind == ARRAY && s->type->array.elem_type->kind != BASIC) {
            flag = false;
        }
        else if(s->type->kind == STRUCTURE) {
            if(! structure_arrays(s->type->structure)) {
                flag = false;
            }
        }
        s = s->next;
    }
    return flag;
}

bool legal_to_output() {
    bool flag = true;
    for(int i = 0;i < TABLE_SIZE; i++) {
        struct SymbolTableItem *p = symbol_table[i];
        while(p != NULL) {
            struct Symbol *s = p->id;
            if(s->kind == VAR && s->type->kind == ARRAY && s->type->array.elem_type->kind != BASIC) {  
                flag = false;
            }       // high dimensions arrays
            else if(s->kind == PROC) {  // array in arglist
                for(int j = 0;j < MAX_ARGS;j++) {
                    if(s->proc_type.argtype_list[j] != NULL && s->proc_type.argtype_list[j]->kind == ARRAY) {
                        flag = false;
                    }
                }
            }           
            else if(s->kind == STRUCTURE) {  // high dimensions array in structure
                if(! structure_arrays(s->type->structure)) {
                    flag = false;
                }
            }
            p = p->next;
        }
    }
    return flag;
}