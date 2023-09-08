#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct VectorClock{
    int dim;
    int tid;
    int* clocks;
};

typedef struct VectorClock* VectorClock_T;

VectorClock_T init(int dim){
    VectorClock_T vc_new;
    vc_new = (VectorClock_T) malloc(sizeof *vc_new);

    vc_new->dim = dim;
    vc_new->tid = -1;
    vc_new->clocks = (int*) malloc(dim * (sizeof(int)));
    memset(vc_new->clocks, 0, dim * (sizeof *(vc_new->clocks)));

    return vc_new;
}

VectorClock_T init_tid(int dim, int tid){
    VectorClock_T vc_new;
    vc_new = (VectorClock_T) malloc(sizeof *vc_new);

    vc_new->dim = dim;
    vc_new->tid = tid;
    vc_new->clocks = (int*) malloc(dim * (sizeof(int)));
    memset(vc_new->clocks, 0, dim * (sizeof *(vc_new->clocks)));

    (vc_new->clocks)[tid] = 1;

    return vc_new;
}

void increment_clock(VectorClock_T self, int delta){
    (self->clocks)[self->tid] += delta;
}

void write_clock(VectorClock_T self, int val){
    (self->clocks)[self->tid] = val;
}

int read_clock(VectorClock_T self, int tid){
    return (self->clocks)[tid];
}

int is_less_than_or_equal(VectorClock_T self, VectorClock_T vc){
    int cl = read_clock(self, self->tid);
    int cr = read_clock(vc, self->tid);
    return cl <= cr;
}

void join(VectorClock_T self, VectorClock_T vc) {
    for(int i = 0; i < self->dim; i++) {
        int clk1 = (self->clocks)[i];
        int clk2 = (vc->clocks)[i];
        (self->clocks)[i] = (clk1 > clk2) ? clk1 : clk2;
    }
}

void copy(VectorClock_T self, VectorClock_T vc) {
    for(int i = 0; i < self->dim; i++) {
        (self->clocks)[i] = (vc->clocks)[i];
    }
}
