// using normal datatypes instead of memory-friendly ones

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

// #define get_tid(x) (x-1)
// #define set_tid(x) (x+1)
#define get_tid(x) (x)
#define set_tid(x) (x)
#define get_node(tree_this, tid) ((tree_this->tree) + tid)
#define get_clock(tree_this, tid) ((tree_this->clocks) + tid)

#define NODE_NULL -1

struct Node {
    int node_next;
    int node_prev;
    int node_par;
    int node_headch;
};

// TODO can also be written as all field == 0
int node_is_null(struct Node* nd){
    return nd->node_next == NODE_NULL && nd->node_prev == NODE_NULL && 
        nd->node_par == NODE_NULL && nd->node_headch == NODE_NULL;
}

// typedef struct Node* Node_T;
/*
void node_set_null(struct Node* nd){
    nd->node_next = -1;
    nd->node_prev = -1;
    nd->node_par = -1;
    nd->node_headch = -1;
}
*/

/*
Node_T clone_node(Node_T nd){
    Node_T nd_new;
    nd_new = (Node_T) malloc(sizeof *nd_new);
    memcpy(nd_new, nd, sizeof *nd_new);
    return nd_new;
}
*/

struct Clock {
    int clock_clk;
    int clock_aclk;
};

// typedef struct Clock* Clock_T;

struct TreeClock{
    int dim;
    int root_tid;
    struct Clock* clocks;
    struct Node* tree;
    int* S;
    int top;
};

typedef struct TreeClock* TreeClock_T;

TreeClock_T tree_clock_init(int dim){
    TreeClock_T tc_new;
    tc_new = (TreeClock_T) malloc(sizeof *tc_new);
    tc_new->root_tid = -1;

    tc_new->dim = dim;
    tc_new->clocks = (struct Clock*) malloc(dim * (sizeof *(tc_new->clocks)));
    tc_new->tree = (struct Node*) malloc(dim * (sizeof *(tc_new->tree)));
    tc_new->S = (int*) malloc(dim * (sizeof *(tc_new->S)));
    tc_new->top = -1;

    memset(tc_new->clocks, 0, dim * (sizeof *(tc_new->clocks)));
    memset(tc_new->tree, 0, dim * (sizeof *(tc_new->tree)));

    return tc_new;
}

// struct Clock* get_clock(TreeClock_T tree_this, int tid){
//     return ((tree_this->clocks) + tid);
// }

// struct Node* get_node(TreeClock_T tree_this, int tid){
//     return ((tree_this->tree) + tid);
// }

void join(TreeClock_T self, TreeClock_T tc){
    int root_tid_this = self->root_tid;

    // originally this check is done at !node_is_null(z_node); would this be better?
    if (root_tid_this == tc->root_tid){
        return ;
    }
    
/*
    if (root_tid_this == zprime_tid || zprime_tid < 0){
        return ;
    }
*/
    // struct Clock* zprime_clocks = get_local_root_data(tc);
    // struct Clock* zprime_clocks = &(tc->clocks[zprime_tid]);

    int zprime_tid = tc->root_tid;
    struct Clock* zprime_clocks = get_clock(tc, zprime_tid);
    // for alignment, this line should be removed.
    //      ... but complete alignment is hard (due to the root check), so skip for now
    int zprime_clock = zprime_clocks->clock_clk;
    struct Node* z_node = get_node(self, zprime_tid);
    struct Clock* z_clocks = get_clock(self, zprime_tid);
    int z_clock = 0;
    // if (!node_is_null(z_node)){
    if (!node_is_null(z_node)){
        z_clock = z_clocks->clock_clk;
        if (zprime_clock <= z_clock){
            return;
/*
        } else {
            detach_from_neighbors(self, zprime_tid, z_node);
*/
        }
        z_clock = z_clocks->clock_clk;
    }

    // z_clocks->clock_clk = zprime_clocks->clock_clk;
    // // copy the clock of this.clocks[this.rootTid] to zprime_clocks's aclk and return
    // z_clocks->clock_aclk = (get_clock(self, root_tid_this))->clock_clk;

    // struct Node* this_root_node = get_node(self, root_tid_this);
    // int root_head_child = get_tid(this_root_node->node_headch);
    // if (root_head_child != -1){
    //     struct Node *ndtmp = get_node(self, root_head_child);
    //     ndtmp->node_prev = set_tid(zprime_tid);
    // }
    // z_node->node_next = set_tid(root_head_child);
    // z_node->node_par = set_tid(root_tid_this);
    // // noop: this.clocks[zprime_tid] = z_clocks;
    // // noop: this.tree[zprime_tid] = z_node;
    // this_root_node->node_headch = set_tid(zprime_tid);

    // int vprime_tid = get_tid((get_node(tc, zprime_tid))->node_headch);
    // while (vprime_tid != 0){
    //     struct Clock* vprime_clocks = get_clock(tc, vprime_tid);
    //     int32_t v_clock = get_local_clock(self, vprime_tid);
    //     if (v_clock < vprime_clocks->clock_clk){
    //         self->S[++self->top] = vprime_tid;
    //     } else {
    //         if (vprime_clocks->clock_aclk <= z_clock){
    //             break;
    //         }
    //     }
    //     vprime_tid = get_tid((get_node(tc, vprime_tid))->node_next);
    // }

    // while (self->top >= 0){
    //     int uprime_tid = self->S[self->top--];
    //     struct Clock* uprime_clocks = get_clock(tc, uprime_tid);
    //     struct Node* u_node = get_node(self, uprime_tid);
    //     struct Clock* u_clocks = get_clock(self, uprime_tid);
    //     int32_t u_clock = 0;

    //     if (!node_is_null(u_node)){
    //         u_clock = u_clocks->clock_clk;
    //         detach_from_neighbors(self, uprime_tid, u_node);
    //     }

    //     // TODO generalize this as clock assignment?
    //     u_clocks->clock_clk = uprime_clocks->clock_clk;
    //     u_clocks->clock_aclk = uprime_clocks->clock_aclk;
        
    //     int y = get_tid((get_node(tc, uprime_tid))->node_par);

    //     struct Node* y_node = get_node(self, y);
    //     int head_child = get_tid(y_node->node_headch);
    //     // here, little change of the condition
    //     if (head_child != -1){
    //         struct Node *ndtmp = get_node(self, head_child);
    //         ndtmp->node_prev = set_tid(uprime_tid);
    //     }
    //     u_node->node_next = set_tid(head_child);
    //     u_node->node_par = set_tid(y);
    //     // noop: this.tree[uprime_tid] = u_node;
    //     y_node->node_headch = set_tid(uprime_tid);

    //     // FIXME: all the same as the while-loop above except for changing z into u
    //     vprime_tid = get_tid((get_node(tc, uprime_tid))->node_headch);
    //     while (vprime_tid != 0){
    //         struct Clock* vprime_clocks = get_clock(tc, vprime_tid);
    //         int32_t v_clock = get_local_clock(self, vprime_tid);
    //         if (v_clock < vprime_clocks->clock_clk){
    //             self->S[++self->top] = vprime_tid;
    //         } else {
    //             if (vprime_clocks->clock_aclk <= u_clock){
    //                 break;
    //             }
    //         }
    //         vprime_tid = get_tid((get_node(tc, vprime_tid))->node_next);
    //     }
    // }
}

