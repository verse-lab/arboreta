#include <stdio.h>
#include "detector_hb.h"
#include "treeclock_ndt.h"
#include "treeclock_ptr.h"
#include "vectorclock.h"

// #define TC
#define PTC
// #define VC

#ifdef TC
#define CLOCK_T                 TreeClock_T
#define init_tid                tc_init_tid
#define init                    tc_init
#define free			tc_free
#define increment_clock         tc_increment_clock
#define read_clock              tc_read_clock
#define write_clock             tc_write_clock
#define join                    tc_join
#define is_less_than_or_equal   tc_is_less_than_or_equal
#define copy                    tc_copy
#endif

#ifdef PTC
#define CLOCK_T                 pTreeClock_T
#define init_tid                ptc_init_tid
#define init                    ptc_init
#define free			ptc_free
#define increment_clock         ptc_increment_clock
#define read_clock              ptc_read_clock
#define write_clock             ptc_write_clock
#define join                    ptc_join
#define is_less_than_or_equal   ptc_is_less_than_or_equal
#define copy                    ptc_copy
#endif

#ifdef VC
#define CLOCK_T                 VectorClock_T
#define init_tid                vc_init_tid
#define init                    vc_init
#define free			vc_free
#define increment_clock         vc_increment_clock
#define read_clock              vc_read_clock
#define write_clock             vc_write_clock
#define join                    vc_join
#define is_less_than_or_equal   vc_is_less_than_or_equal
#define copy                    vc_copy
#endif

CLOCK_T thread_clk[MAX_THREADS];
VectorClock_T read_clk[MAX_VARS];
CLOCK_T write_clk[MAX_VARS];
CLOCK_T lock_clk[MAX_LOCKS];

int threads_num;
int vars_num;
int locks_num;

void init_detector(int tnum, int vnum, int lnum) {
    threads_num = tnum;
    vars_num = vnum;
    locks_num = lnum;
    for(int i = 0; i < threads_num; i++) {
        thread_clk[i] = init_tid(threads_num, i);
    }
    for(int i = 0; i < vars_num; i++) {
        read_clk[i] = vc_init(threads_num);
        write_clk[i] = init(threads_num);
    }
    for(int i = 0; i < locks_num; i++) {
        lock_clk[i] = init(threads_num);
    }
}

void free_detector() {
    for(int i = 0; i < threads_num; i++) {
        free(thread_clk[i]);
    }
    for(int i = 0; i < vars_num; i++) {
        vc_free(read_clk[i]);
        free(write_clk[i]);
    }
    for(int i = 0; i < locks_num; i++) {
        free(lock_clk[i]);
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
            copy(lock_clk[e->lock], thread_clk[e->thread]);
            increment_clock(thread_clk[e->thread], 1);
            break;
        case FORK:
            join(thread_clk[e->thr2], thread_clk[e->thread]);
            increment_clock(thread_clk[e->thread], 1);
            break;
        case JOIN:
            join(thread_clk[e->thread], thread_clk[e->thr2]);
            increment_clock(thread_clk[e->thr2], 1);
            break;
        case READ:
            if(vc_read_clock(read_clk[e->var], e->thread) != read_clock(thread_clk[e->thread], e->thread)) {
                if(is_less_than_or_equal(write_clk[e->var], thread_clk[e->thread])) {
                    vc_write_clock(read_clk[e->var], e->thread, read_clock(thread_clk[e->thread], e->thread));
                }
                else {
                    is_race = 1;
                }
            }
            break;
        case WRITE:
            if(read_clock(write_clk[e->var], e->thread) != read_clock(thread_clk[e->thread], e->thread)) {
                if(is_less_than_or_equal(write_clk[e->var], thread_clk[e->thread])) {    
                    for(int i = 0; i < threads_num; i++) {
                        int cl = vc_read_clock(read_clk[e->var], i);
                        int cr = read_clock(thread_clk[e->thread], i);
                        if(cl > cr) {
                            is_race = 1;
                            break;
                        }
                    }
                    if(!is_race) {
                        copy(write_clk[e->var], thread_clk[e->thread]);
                    }
                }
                else {
                    is_race = 1;
                }
            }
            break;
        default:
            break;
    }
    return is_race;
}
