// using normal datatypes instead of memory-friendly ones

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "treeclock_ptr.h"
#include "data_structure.h"

pTreeClock_T ptc_init(int dim){
    pTreeClock_T tc_new;
    tc_new = (pTreeClock_T) malloc(sizeof *tc_new);
    tc_new->root_tid = -1;

    tc_new->dim = dim;
    tc_new->S = (struct pNode**) malloc(dim * (sizeof *(tc_new->S)));
    tc_new->top = -1;

    tc_new->tree = (struct pNode*) malloc(sizeof *(tc_new->tree));
    struct pNode* ptr = tc_new->tree;
    for(int i = 0; i < dim - 1; i++) {
        ptr->node_next = (struct pNode*) malloc(sizeof *(tc_new->tree));
        ptr = ptr->node_next;
    }

    return tc_new;
}

pTreeClock_T ptc_init_tid(int dim, int tid){
    pTreeClock_T tc_new;
    tc_new = (pTreeClock_T) malloc(sizeof *tc_new);
    tc_new->root_tid = tid;

    tc_new->dim = dim;
    tc_new->S = (struct pNode**) malloc(dim * (sizeof *(tc_new->S)));
    tc_new->top = -1;

    tc_new->tree = (struct pNode*) malloc(sizeof *(tc_new->tree));
    tc_new->tree->tid = tid;
    tc_new->tree->node_par = NULL;
    tc_new->tree->node_next = NULL;
    tc_new->tree->node_prev = NULL;
    tc_new->tree->clock_clk = 1;

    struct pNode* ptr = NULL;
    struct pNode* next_ptr = NULL;
    for(int i = 0; i < dim; i++) {
        if(i == tid) {
            continue;
        }
        ptr = (struct pNode*) malloc(sizeof *(tc_new->tree));
        ptr->tid = i;
        ptr->clock_clk = 0;
        ptr->clock_aclk = 0;
        ptr->node_par = tc_new->tree;
        ptr->node_next = next_ptr;
        ptr->node_prev = NULL;
        ptr->node_headch = NULL;
        if(next_ptr != NULL) {
            next_ptr->node_prev = ptr;
        }
        next_ptr = ptr;
    }
    tc_new->tree->node_headch = next_ptr;

    return tc_new;
}

int* ptc_get_clock(pTreeClock_T tc, int tid) {
    struct pNode* working[tc->dim];
    int top = -1;

    working[++top] = tc->tree;

    while(top >= 0) {
        struct pNode* node = working[top--];
        if(node->tid == tid) {
            return &(node->clock_clk);
        }
        if(node->node_next != NULL){
            working[++top] = node->node_next;
        }
        if(node->node_headch != NULL) {
            working[++top] = node->node_headch;
        }   
    }
    return NULL;
}

struct pNode* ptc_get_node(pTreeClock_T tc, int tid) {
    struct pNode* working[tc->dim];
    int top = -1;

    working[++top] = tc->tree;

    while(top >= 0) {
        struct pNode* node = working[top--];
        if(node->tid == tid) {
            return node;
        }
        if(node->node_next != NULL){
            working[++top] = node->node_next;
        }
        if(node->node_headch != NULL) {
            working[++top] = node->node_headch;
        }   
    }
    return NULL;
}

void ptc_increment_clock(pTreeClock_T self, int delta){
    int* c = ptc_get_clock(self, self->root_tid);
    *c += delta;
}

void ptc_write_clock(pTreeClock_T self, int val){
    int* c = ptc_get_clock(self, self->root_tid);
    *c = val;
}

int ptc_read_clock(pTreeClock_T self, int tid){
    if(self->root_tid < 0) {
        return 0;
    }
    int* c = ptc_get_clock(self, tid);
    return *c;
}

int ptc_is_less_than_or_equal(pTreeClock_T self, pTreeClock_T tc){
    int root_tid = self->root_tid;
    if(root_tid < 0) {
        return 1;
    }
    int cl = ptc_read_clock(self, root_tid);
    int cr = ptc_read_clock(tc, root_tid);
    return cl <= cr;
}

void ptc_detach_from_neighbors(pTreeClock_T self, int t, struct pNode* nd){
    if (nd->node_par->node_headch->tid == t) {
        nd->node_par->node_headch = nd->node_next;
    } else {
        nd->node_prev->node_next = nd->node_next;
    }

    if (nd->node_next != NULL) {
        nd->node_next->node_prev = nd->node_prev;
    }
}

void ptc_push_child(pTreeClock_T self, int par, int t, struct pNode* nd){
    struct pNode* par_node = ptc_get_node(self, par);
    if (par_node->node_headch != NULL){
        par_node->node_headch->node_prev = nd;
    }
    // this is not in the original paper (since prev is not used so it is still okay if prev is not maintained?), but add it here anyway
    nd->node_prev = NULL;
    nd->node_next = par_node->node_headch;
    nd->node_par = par_node;
    par_node->node_headch = nd;
}

void ptc_get_updated_nodes_join_chn(pTreeClock_T self, pTreeClock_T tc, int par, int par_clock){
    struct pNode* nd_par = ptc_get_node(tc, par);
    struct pNode* ptr = nd_par->node_headch;
    while (ptr != NULL){
        struct pNode* vprime_clocks = ptc_get_node(tc, ptr->tid);
        struct pNode* v_clocks = ptc_get_node(self, ptr->tid);
        if (v_clocks->clock_clk < vprime_clocks->clock_clk){
            self->S[++self->top] = ptr;
        } else {
            if (vprime_clocks->clock_aclk <= par_clock){
                break;
            }
        }
        ptr = ptr->node_next;
    }
}

void ptc_join(pTreeClock_T self, pTreeClock_T tc){
    int root_tid_this = self->root_tid;
    // possibly would be better to early return, but not sure; this is closer to the Java code, anyway
    if (root_tid_this == tc->root_tid || tc->root_tid < 0){
        return;
    }

    int zprime_tid = tc->root_tid;
    // for alignment, this line should be removed.
    //      ... but complete alignment is hard (due to the root check), so skip for now
    int zprime_clock = *ptc_get_clock(tc, zprime_tid);
    struct pNode* z_node = ptc_get_node(self, zprime_tid);


    int z_clock = z_node->clock_clk;
    if (zprime_clock <= z_clock){
        return;
    } else {
        ptc_detach_from_neighbors(self, zprime_tid, z_node);
    }


    // TODO generalize this as clock assignment?
    z_node->clock_clk = zprime_clock; /* local optimization */
    z_node->clock_aclk = *ptc_get_clock(self, root_tid_this);
    ptc_push_child(self, root_tid_this, zprime_tid, z_node);
    ptc_get_updated_nodes_join_chn(self, tc, zprime_tid, z_clock);

    while (self->top >= 0){
        int uprime_tid = self->S[self->top--]->tid;
        struct pNode* uprime_node = ptc_get_node(tc, uprime_tid);
        struct pNode* u_node = ptc_get_node(self, uprime_tid);
        int u_clock = u_node->clock_clk;

        ptc_detach_from_neighbors(self, uprime_tid, u_node);
        u_node->clock_clk = uprime_node->clock_clk;
        u_node->clock_aclk = uprime_node->clock_aclk;
        int y = uprime_node->node_par->tid;
        ptc_push_child(self, y, uprime_tid, u_node); 
        ptc_get_updated_nodes_join_chn(self, tc, uprime_tid, u_clock);
    }
}


void ptc_copy(pTreeClock_T self, pTreeClock_T from_tree_clock){
    self->root_tid = from_tree_clock->root_tid;

    struct pNode freelist;
    if(self->root_tid < 0) {
        freelist.node_next = self->tree;
    }
    else {
        struct pNode* ptr = &freelist;
        struct pNode* working[self->dim];
        int top = -1;

        working[++top] = self->tree;

        while(top >= 0) {
            struct pNode* node = working[top--];
            if(node->node_next != NULL){
                working[++top] = node->node_next;
            }
            if(node->node_headch != NULL) {
                working[++top] = node->node_headch;
            }
            ptr->node_next = node;
            ptr = node;
        }
    }
    
    struct pNode* working1[self->dim];
    struct pNode* working2[self->dim];
    int top1 = -1, top2 = -1;
    working1[++top1] = from_tree_clock->tree;
    working2[++top2] = freelist.node_next;
    
    struct pNode* ptr1 = freelist.node_next;
    freelist.node_next = ptr1->node_next;
    ptr1->tid = from_tree_clock->tree->tid;
    ptr1->clock_clk = from_tree_clock->tree->clock_clk;
    ptr1->clock_aclk = from_tree_clock->tree->clock_aclk;
    ptr1->node_next = NULL;
    ptr1->node_prev = NULL;
    ptr1->node_par = NULL;
    ptr1->node_headch = NULL;

    while(top1 >= 0) {
        struct pNode* node1 = working1[top1--];
        struct pNode* node2 = working2[top2--];
        if(node1->node_next != NULL){
            working1[++top1] = node1->node_next;
            working2[++top2] = freelist.node_next;
            struct pNode* ptr1 = freelist.node_next;
            freelist.node_next = ptr1->node_next;
            node2->node_next = ptr1;
            ptr1->node_prev = node2;
            ptr1->node_next = NULL;
            ptr1->node_par = node2->node_par;
            ptr1->node_headch = NULL;
            ptr1->tid = node1->node_next->tid;
            ptr1->clock_clk = node1->node_next->clock_clk;
            ptr1->clock_aclk = node1->node_next->clock_aclk;
        }
        if(node1->node_headch != NULL) {
            working1[++top1] = node1->node_headch;
            working2[++top2] = freelist.node_next;
            struct pNode* ptr1 = freelist.node_next;
            freelist.node_next = ptr1->node_next;
            node2->node_headch = ptr1;
            ptr1->node_par = node2;
            ptr1->node_next = NULL;
            ptr1->node_prev = NULL;
            ptr1->node_headch = NULL;
            ptr1->tid = node1->node_headch->tid;
            ptr1->clock_clk = node1->node_headch->clock_clk;
            ptr1->clock_aclk = node1->node_headch->clock_aclk;
        }
    }
}

void ptc_print(pTreeClock_T tc) {
    struct pNode* working[tc->dim];
    int top = -1;
    printf("root: %d\n", tc->root_tid);
    working[++top] = tc->tree;

    while(top >= 0) {
        struct pNode* node = working[top--];
        printf("t%d:c%d:", node->tid, node->clock_clk);
        if(node->node_next != NULL){
            working[++top] = node->node_next;
            printf("n%d:", node->node_next->tid);
        }
        if(node->node_headch != NULL) {
            working[++top] = node->node_headch;
            printf("c%d:", node->node_headch->tid);
        }   
        printf(" ");
    }
    printf("\n");
}
