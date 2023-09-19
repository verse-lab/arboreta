#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "data_structure.h"
#include "vectorclock.h"

VectorClock_T vc_init(int dim){
    VectorClock_T vc_new;
    vc_new = (VectorClock_T) malloc(sizeof *vc_new);

    vc_new->dim = dim;
    vc_new->tid = -1;
    vc_new->clocks = (int*) malloc(dim * (sizeof(int)));
    memset(vc_new->clocks, 0, dim * (sizeof(int)));

    return vc_new;
}

VectorClock_T vc_init_tid(int dim, int tid){
    VectorClock_T vc_new;
    vc_new = (VectorClock_T) malloc(sizeof *vc_new);

    vc_new->dim = dim;
    vc_new->tid = tid;
    vc_new->clocks = (int*) malloc(dim * (sizeof(int)));
    memset(vc_new->clocks, 0, dim * (sizeof(int)));

    (vc_new->clocks)[tid] = 1;

    return vc_new;
}

void vc_increment_clock(VectorClock_T self, int delta){
    (self->clocks)[self->tid] += delta;
}

void vc_write_clock(VectorClock_T self, int tid, int val){
    (self->clocks)[tid] = val;
}

int vc_read_clock(VectorClock_T self, int tid){
    return (self->clocks)[tid];
}

int vc_is_less_than_or_equal(VectorClock_T self, VectorClock_T vc){
    if(self->tid < 0) {
        return 1;
    }
    int cl = vc_read_clock(self, self->tid);
    int cr = vc_read_clock(vc, self->tid);
    return cl <= cr;
}

void vc_join(VectorClock_T self, VectorClock_T vc) {
    if(self->tid == -1) {
        self->tid = vc->tid;
    }
    for(int i = 0; i < self->dim; i++) {
        int clk1 = (self->clocks)[i];
        int clk2 = (vc->clocks)[i];
        (self->clocks)[i] = (clk1 > clk2) ? clk1 : clk2;
    }
}

void vc_copy(VectorClock_T self, VectorClock_T vc) {
    for(int i = 0; i < self->dim; i++) {
        (self->clocks)[i] = (vc->clocks)[i];
    }
    self->tid = vc->tid;
}
