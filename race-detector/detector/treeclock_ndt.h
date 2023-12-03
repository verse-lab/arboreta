#ifndef _HEADER_TREECLOCK_NDT_H
#define _HEADER_TREECLOCK_NDT_H

struct Node {
    int node_next;
    int node_prev;
    int node_par;
    int node_headch;
};

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

TreeClock_T tc_init(int dim);
TreeClock_T tc_init_tid(int dim, int tid);
void tc_free(TreeClock_T tc);
void tc_increment_clock(TreeClock_T self, int delta);
void tc_write_clock(TreeClock_T self, int val);
int tc_read_clock(TreeClock_T self, int tid);
int tc_is_less_than_or_equal(TreeClock_T self, TreeClock_T tc);
void tc_join(TreeClock_T self, TreeClock_T tc);
void tc_copy(TreeClock_T self, TreeClock_T from_tree_clock);

#endif
