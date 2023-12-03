// using normal datatypes instead of memory-friendly ones

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "treeclock_ptr.h"
#include "data_structure.h"

void ptc_set_pNode(struct pNode* pnd, int tid, int clk, int aclk, 
                   struct pNode* par, struct pNode* next, 
                   struct pNode* prev, struct pNode* headch) {
    pnd->tid = tid;
    pnd->clock_clk = clk;
    pnd->clock_aclk = aclk;
    pnd->node_par = par;
    pnd->node_next = next;
    pnd->node_prev = prev;
    pnd->node_headch = headch;
}

pTreeClock_T ptc_init(int dim){
    pTreeClock_T tc_new;
    tc_new = (pTreeClock_T) malloc(sizeof *tc_new);
    tc_new->root_tid = -1;

    tc_new->dim = dim;
    tc_new->S = (struct pNode**) malloc(dim * (sizeof *(tc_new->S)));
    tc_new->top = -1;

    struct pNode* ptr = tc_new->tree;
    struct pNode* prev = NULL;
    for(int i = 0; i < dim; i++) {
        ptr = (struct pNode*) malloc(sizeof *(tc_new->tree));
        ptc_set_pNode(ptr, i, -1, 0, NULL, NULL, prev, NULL);
        if(prev != NULL) {
            prev->node_next = ptr;
        }
        prev = ptr;
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

    struct pNode* ptr = NULL;
    struct pNode* next_ptr = NULL;
    for(int i = 0; i < dim; i++) {
        if(i == tid) {
            continue;
        }
        ptr = (struct pNode*) malloc(sizeof *(tc_new->tree));
        ptc_set_pNode(ptr, i, 0, 0, tc_new->tree, next_ptr, NULL, NULL);
        if(next_ptr != NULL) {
            next_ptr->node_prev = ptr;
        }
        next_ptr = ptr;
    }
    ptc_set_pNode(tc_new->tree, tid, 1, -1, NULL, NULL, NULL, next_ptr);

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

void ptc_free(pTreeClock_T tc) {
    free(tc->S);
    struct pNode* working[tc->dim];
    int top = -1;

    working[++top] = tc->tree;

    while(top >= 0) {
        struct pNode* node = working[top--];
        if(node->node_next != NULL){
            working[++top] = node->node_next;
        }
        if(node->node_headch != NULL) {
            working[++top] = node->node_headch;
        }   
        free(node);
    }
    free(tc);
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
    nd->node_prev = NULL;
    nd->node_next = par_node->node_headch;
    nd->node_par = par_node;
    par_node->node_headch = nd;
}

void ptc_get_updated_nodes_join_chn(pTreeClock_T self, pTreeClock_T tc, struct pNode* nd_par, int par_clock){
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
    if (self->root_tid == tc->root_tid || tc->root_tid < 0){
        return;
    }

    if (*ptc_get_clock(tc, tc->root_tid) <= *ptc_get_clock(self, tc->root_tid)){
        return;
    }

    self->S[++self->top] = ptc_get_node(self, tc->root_tid);

    while (self->top >= 0){
        int uprime_tid = self->S[self->top--]->tid;
        struct pNode* uprime_node = ptc_get_node(tc, uprime_tid);
        struct pNode* u_node = ptc_get_node(self, uprime_tid);
        int u_clock = u_node->clock_clk;

        ptc_detach_from_neighbors(self, uprime_tid, u_node);
        u_node->clock_clk = uprime_node->clock_clk;
        u_node->clock_aclk = uprime_node->clock_aclk;
        int par_tid;
        if(uprime_node->node_par == NULL) {
            par_tid = self->root_tid;
        }
        else {
            par_tid = uprime_node->node_par->tid;
        }
        ptc_push_child(self, par_tid, uprime_tid, u_node); 
        ptc_get_updated_nodes_join_chn(self, tc, uprime_node, u_clock);
    }
}


// void ptc_copy(pTreeClock_T self, pTreeClock_T from_tree_clock){
//     self->root_tid = from_tree_clock->root_tid;
//     struct pNode freelist;
//     if(self->root_tid < 0) {
//         freelist.node_next = self->tree;
//     }
//     else {
//         struct pNode* ptr = &freelist;
//         struct pNode* working[self->dim];
//         int top = -1;

//         working[++top] = self->tree;

//         while(top >= 0) {
//             struct pNode* node = working[top--];
//             if(node->node_next != NULL){
//                 working[++top] = node->node_next;
//             }
//             if(node->node_headch != NULL) {
//                 working[++top] = node->node_headch;
//             }
//             ptr->node_next = node;
//             ptr = node;
//         }
//     }
    
//     struct pNode* working1[self->dim];
//     struct pNode* working2[self->dim];
//     int top1 = -1, top2 = -1;
//     working1[++top1] = from_tree_clock->tree;
//     working2[++top2] = freelist.node_next;
    
//     struct pNode* ptr1 = freelist.node_next;
//     freelist.node_next = ptr1->node_next;
//     ptc_set_pNode(ptr1, from_tree_clock->tree->tid, 
//                   from_tree_clock->tree->clock_clk, from_tree_clock->tree->clock_aclk,
//                   NULL, NULL, NULL, NULL);

//     while(top1 >= 0) {
//         struct pNode* node1 = working1[top1--];
//         struct pNode* node2 = working2[top2--];
//         if(node1->node_next != NULL){
//             working1[++top1] = node1->node_next;
//             working2[++top2] = freelist.node_next;
//             struct pNode* ptr1 = freelist.node_next;
//             freelist.node_next = ptr1->node_next;
//             node2->node_next = ptr1;
//             ptc_set_pNode(ptr1, node1->node_next->tid, node1->node_next->clock_clk, node1->node_next->clock_aclk,
//                           node2->node_par, NULL, node2, NULL);
//         }
//         if(node1->node_headch != NULL) {
//             working1[++top1] = node1->node_headch;
//             working2[++top2] = freelist.node_next;
//             struct pNode* ptr1 = freelist.node_next;
//             freelist.node_next = ptr1->node_next;
//             node2->node_headch = ptr1;
//             ptc_set_pNode(ptr1, node1->node_headch->tid, node1->node_headch->clock_clk, node1->node_headch->clock_aclk,
//                           node2, NULL, NULL, NULL);
//         }
//     }
// }

void ptc_print(pTreeClock_T tc) {
    struct pNode* working[tc->dim];
    int top = -1;
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
            printf("ch%d:", node->node_headch->tid);
        }   
        printf(" ");
    }
    printf("\n");
}
