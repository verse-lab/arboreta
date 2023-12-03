#ifndef _HEADER_TREECLOCK_PTR_H
#define _HEADER_TREECLOCK_PTR_H

struct pNode {
    int tid;
    int clock_clk;
    int clock_aclk;
    struct pNode* node_next;
    struct pNode* node_prev;
    struct pNode* node_par;
    struct pNode* node_headch;
};

struct pTreeClock{
    int dim;
    int root_tid;
    struct pNode* tree;
    struct pNode** S;
    int top;
};

typedef struct pTreeClock* pTreeClock_T;

pTreeClock_T ptc_init(int dim);
pTreeClock_T ptc_init_tid(int dim, int tid);
void ptc_free(pTreeClock_T tc);
void ptc_increment_clock(pTreeClock_T self, int delta);
void ptc_write_clock(pTreeClock_T self, int val);
int ptc_read_clock(pTreeClock_T self, int tid);
int ptc_is_less_than_or_equal(pTreeClock_T self, pTreeClock_T tc);
void ptc_join(pTreeClock_T self, pTreeClock_T tc);
void ptc_copy(pTreeClock_T self, pTreeClock_T from_tree_clock);
void ptc_print(pTreeClock_T tc);

#endif
