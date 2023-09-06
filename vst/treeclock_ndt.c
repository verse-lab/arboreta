// using normal datatypes instead of memory-friendly ones

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/*
    General known issues: 
    - it is expensive to read tree_this->tree or tree_this->clocks each time
    - the field `prev` is not used at all (and also seems not maintained well)
    - cannot handle reading a struct and its field at the same time, e.g.: (get_node(tc, uprime_tid))->node_par
    - the case where a tree is empty (i.e., roottid < 0) is not handled in any function; actually not sure whether it should be handled or not, since it sounds reasonable to simply make an empty tree be a single root node with clock = 0
*/

#define get_tid(x) (x)
#define set_tid(x) (x)
// the following expressions are seemingly equivalent with &(tree_this->...[...]) in Clight
#define get_node(tree_this, tid) ((tree_this->tree) + tid)
#define get_clock(tree_this, tid) ((tree_this->clocks) + tid)

#define NODE_NULL -1

struct Node {
    int node_next;
    int node_prev;
    int node_par;
    int node_headch;
};

int node_is_null(struct Node* nd){
    return nd->node_next == NODE_NULL && nd->node_prev == NODE_NULL && 
        nd->node_par == NODE_NULL && nd->node_headch == NODE_NULL;
}

struct Clock {
    int clock_clk;
    int clock_aclk;
};

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

void increment_clock(TreeClock_T self, int delta){
    struct Clock* c = get_clock(self, self->root_tid);
    c->clock_clk += delta;
}

void write_clock(TreeClock_T self, int val){
    struct Clock* c = get_clock(self, self->root_tid);
    c->clock_clk = val;
}

int read_clock(TreeClock_T self, int tid){
    struct Clock* c = get_clock(self, tid);
    return c->clock_clk;
}

int is_less_than_or_equal(TreeClock_T self, TreeClock_T tc){
    int root_tid = self->root_tid;
    int cl = read_clock(self, root_tid);
    int cr = read_clock(tc, root_tid);
    return cl <= cr;
}

void detach_from_neighbors(TreeClock_T self, int t, struct Node* nd){
    int t_next = get_tid(nd->node_next);
    int t_prev = get_tid(nd->node_prev);
    int t_parent = get_tid(nd->node_par);

    // this is not required, but would possibly make things slightly easier if this function is used somewhere else
    // nd->node_next = NODE_NULL;
    // nd->node_prev = NODE_NULL;
    // nd->node_par = NODE_NULL;

    struct Node* parent_node = get_node(self, t_parent);

    if (get_tid(parent_node->node_headch) == t) {
        parent_node->node_headch = set_tid(t_next);
    } else {
        struct Node* prev_node = get_node(self, t_prev);
        prev_node->node_next = set_tid(t_next);
    }

    if (t_next != NODE_NULL) {
        struct Node* next_node = get_node(self, t_next);
        next_node->node_prev = set_tid(t_prev);
    }
}

void push_child(TreeClock_T self, int par, int t, struct Node* nd){
    struct Node* par_node = get_node(self, par);
    int head_child = get_tid(par_node->node_headch);
    if (head_child != NODE_NULL){
        struct Node *ndtmp = get_node(self, head_child);
        ndtmp->node_prev = set_tid(t);
    }
    // this is not in the original paper (since prev is not used so it is still okay if prev is not maintained?), but add it here anyway
    nd->node_prev = NODE_NULL;
    
    nd->node_next = set_tid(head_child);
    nd->node_par = set_tid(par);
    par_node->node_headch = set_tid(t);
}

void get_updated_nodes_join_chn(TreeClock_T self, TreeClock_T tc, int par, int par_clock){
    struct Node* nd_par = get_node(tc, par);
    int vprime_tid = get_tid(nd_par->node_headch);
    while (vprime_tid != NODE_NULL){
        struct Clock* vprime_clocks = get_clock(tc, vprime_tid);
        struct Clock* v_clocks = get_clock(self, vprime_tid);
        int v_clock = v_clocks->clock_clk;
        if (v_clock < vprime_clocks->clock_clk){
            self->S[++self->top] = vprime_tid;
        } else {
            if (vprime_clocks->clock_aclk <= par_clock){
                break;
            }
        }
        struct Node* nd = get_node(tc, vprime_tid);
        vprime_tid = get_tid(nd->node_next);
    }
}

void join(TreeClock_T self, TreeClock_T tc){
    int root_tid_this = self->root_tid;

    // possibly would be better to early return, but not sure; this is closer to the Java code, anyway
    if (root_tid_this == tc->root_tid){
        return ;
    }

    int zprime_tid = tc->root_tid;
    struct Clock* zprime_clocks = get_clock(tc, zprime_tid);
    // for alignment, this line should be removed.
    //      ... but complete alignment is hard (due to the root check), so skip for now
    int zprime_clock = zprime_clocks->clock_clk;
    struct Node* z_node = get_node(self, zprime_tid);
    struct Clock* z_clocks = get_clock(self, zprime_tid);

    int z_clock = z_clocks->clock_clk;
    if (zprime_clock <= z_clock){
        return;
    } else if (!node_is_null(z_node)){
        detach_from_neighbors(self, zprime_tid, z_node);
    }

    // TODO generalize this as clock assignment?
    z_clocks->clock_clk = zprime_clock; /* local optimization */
    struct Clock* self_root_clocks = get_clock(self, root_tid_this);
    z_clocks->clock_aclk = self_root_clocks->clock_clk;

    push_child(self, root_tid_this, zprime_tid, z_node);

    get_updated_nodes_join_chn(self, tc, zprime_tid, z_clock);

    while (self->top >= 0){
        int uprime_tid = self->S[self->top--];
        struct Clock* uprime_clocks = get_clock(tc, uprime_tid);
        struct Node* u_node = get_node(self, uprime_tid);
        struct Clock* u_clocks = get_clock(self, uprime_tid);
        int u_clock = u_clocks->clock_clk;

        if (!node_is_null(u_node)){
            detach_from_neighbors(self, uprime_tid, u_node);
        }

        u_clocks->clock_clk = uprime_clocks->clock_clk;
        u_clocks->clock_aclk = uprime_clocks->clock_aclk;
        
        struct Node* uprime_node = get_node(tc, uprime_tid);
        int y = get_tid(uprime_node->node_par);

        push_child(self, y, uprime_tid, u_node); 

        get_updated_nodes_join_chn(self, tc, uprime_tid, u_clock);
    }
}

void get_updated_nodes_copy_chn(TreeClock_T self, TreeClock_T tc, int par, int par_clock, int targ){
    struct Node* nd_par = get_node(tc, par);
    int vprime_tid = get_tid(nd_par->node_headch);
    while (vprime_tid != NODE_NULL){
        struct Clock* vprime_clocks = get_clock(tc, vprime_tid);
        struct Clock* v_clocks = get_clock(self, vprime_tid);
        int v_clock = v_clocks->clock_clk;
        if (v_clock < vprime_clocks->clock_clk){
            self->S[++self->top] = vprime_tid;
        } else {
            if (vprime_tid == targ){
                self->S[++self->top] = vprime_tid;
            } else if (vprime_clocks->clock_aclk <= par_clock){
                break;
            }
        }
        struct Node* nd = get_node(tc, vprime_tid);
        vprime_tid = get_tid(nd->node_next);
    }
}

void monotone_copy(TreeClock_T self, TreeClock_T tc){
    int root_tid_this = self->root_tid;

    int zprime_tid = tc->root_tid;
    struct Clock* zprime_clocks = get_clock(tc, zprime_tid);
    struct Node* z_node = get_node(self, zprime_tid);
    struct Clock* z_clocks = get_clock(self, zprime_tid);

    int z_clock = z_clocks->clock_clk;
    if (!node_is_null(z_node)){
        if (zprime_tid != root_tid_this){
            detach_from_neighbors(self, zprime_tid, z_node);
        }
    }

    z_clocks->clock_clk = zprime_clocks->clock_clk;
    z_clocks->clock_aclk = zprime_clocks->clock_aclk;       // TODO is this really necessary?
    z_node->node_par = NODE_NULL;
    z_node->node_prev = NODE_NULL;          // seems necessary to keep tree shape
    z_node->node_next = NODE_NULL;          // seems necessary to keep tree shape

    get_updated_nodes_copy_chn(self, tc, zprime_tid, z_clock, root_tid_this);

    while (self->top >= 0){
        int uprime_tid = self->S[self->top--];
        struct Clock* uprime_clocks = get_clock(tc, uprime_tid);
        struct Node* u_node = get_node(self, uprime_tid);
        struct Clock* u_clocks = get_clock(self, uprime_tid);
        int u_clock = u_clocks->clock_clk;

        if (!node_is_null(u_node)){
            if (uprime_tid != root_tid_this){
                detach_from_neighbors(self, uprime_tid, u_node);
            }
        }

        u_clocks->clock_clk = uprime_clocks->clock_clk;
        u_clocks->clock_aclk = uprime_clocks->clock_aclk;
        
        struct Node* uprime_node = get_node(tc, uprime_tid);
        int y = get_tid(uprime_node->node_par);

        push_child(self, y, uprime_tid, u_node); 

        get_updated_nodes_copy_chn(self, tc, uprime_tid, u_clock, root_tid_this);
    }

    self->root_tid = zprime_tid;            // TODO will this make things easier or harder?
}
