#include <stdio.h>
#include "detector.h"
// #include "treeclock_ndt.c"
#include "vectorclock.c"

// #define CLOCK_T struct TreeClock
#define CLOCK_T VectorClock_T

CLOCK_T thread_clk[MAX_THREADS];
CLOCK_T read_clk[MAX_VARS];
CLOCK_T write_clk[MAX_VARS];
CLOCK_T lock_clk[MAX_LOCKS];

void init_detector() {
    for(int i = 0; i < MAX_THREADS; i++) {
        thread_clk[i] = init_tid(MAX_THREADS, i);
    }
    for(int i = 0; i < MAX_VARS; i++) {
        read_clk[i] = init(MAX_THREADS);
        write_clk[i] = init(MAX_THREADS);
    }
    for(int i = 0; i < MAX_LOCKS; i++) {
        lock_clk[i] = init(MAX_THREADS);
    }
}

int detect(Event* e) {
    int is_race = 0;
    switch (e->type)
    {
        case ACQUIRE:
            join(thread_clk[e->thread], lock_clk[e->lock]);
            break;
        case RELEASE:
            increment_clock(thread_clk[e->thread], 1);
            copy(lock_clk[e->lock], thread_clk[e->thread]);
            break;
        case FORK:
            increment_clock(thread_clk[e->thread], 1);
            join(thread_clk[e->thr2], thread_clk[e->thread]);
            break;
        case JOIN:
            increment_clock(thread_clk[e->thr2], 1);
            join(thread_clk[e->thread], thread_clk[e->thr2]);
            break;
        case READ:
            if(is_less_than_or_equal(write_clk[e->var], thread_clk[e->thread])) {
                // think of this
                write_clock(read_clk[e->var], read_clock(thread_clk[e->thread], e->thread));
            }
            else if(read_clock(read_clk[e->var], e->thread) != read_clock(thread_clk[e->var], e->thread)) {
                is_race = 1;
            }
            break;
        case WRITE:
            if(is_less_than_or_equal(write_clk[e->var], thread_clk[e->thread])
                && is_less_than_or_equal(read_clk[e->var], thread_clk[e->thread])) {
                // think of this
                write_clock(write_clk[e->var], read_clock(thread_clk[e->thread], e->thread));
            }
            else if(read_clock(write_clk[e->var], e->thread) != read_clock(thread_clk[e->var], e->thread)) {
                is_race = 1;
            }
            break;
        default:
            break;
    }
    return is_race;
}