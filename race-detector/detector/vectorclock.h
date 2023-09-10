#ifndef _HEADER_VECTORCLOCK_H
#define _HEADER_VECTORCLOCK_H

struct VectorClock{
    int dim;
    int tid;
    int* clocks;
};

typedef struct VectorClock* VectorClock_T;

VectorClock_T vc_init(int dim);
VectorClock_T vc_init_tid(int dim, int tid);
void vc_increment_clock(VectorClock_T self, int delta);
void vc_write_clock(VectorClock_T self, int val);
int vc_read_clock(VectorClock_T self, int tid);
int vc_is_less_than_or_equal(VectorClock_T self, VectorClock_T vc);
void vc_join(VectorClock_T self, VectorClock_T vc);
void vc_monotone_copy(VectorClock_T self, VectorClock_T vc);

#endif