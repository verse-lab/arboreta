#include <stdio.h>
#include "detector_ft.h"
#include "treeclock_ndt.h"
#include "vectorclock.h"

// #define _DEBUG

#define CLOCK_T                 TreeClock_T
#define init_tid                tc_init_tid
#define init                    tc_init
#define increment_clock         tc_increment_clock
#define read_clock              tc_read_clock
#define write_clock             tc_write_clock
#define join                    tc_join
#define is_less_than_or_equal   tc_is_less_than_or_equal
#define monotone_copy           tc_monotone_copy

// #define CLOCK_T                 VectorClock_T
// #define init_tid                vc_init_tid
// #define init                    vc_init
// #define increment_clock         vc_increment_clock
// #define read_clock              vc_read_clock
// #define write_clock             vc_write_clock
// #define join                    vc_join
// #define is_less_than_or_equal   vc_is_less_than_or_equal
// #define monotone_copy           vc_monotone_copy

CLOCK_T thread_clk[MAX_THREADS];
CLOCK_T lock_clk[MAX_LOCKS];

int is_read_epoch;
int read_epochs_thread[MAX_VARS];
VectorClock_T read_epochs_timestamp[MAX_VARS];

int write_epochs_thread[MAX_VARS];
int write_epochs_timestamp[MAX_VARS];

void init_detector() {
    for(int i = 0; i < MAX_THREADS; i++) {
        thread_clk[i] = init_tid(MAX_THREADS, i);
    }
    for(int i = 0; i < MAX_LOCKS; i++) {
        lock_clk[i] = init(MAX_THREADS);
    }
    is_read_epoch = 1;
    for(int i = 0; i < MAX_VARS; i++) {
        read_epochs_thread[i] = 0;
        read_epochs_timestamp[i] = vc_init(MAX_THREADS);
        write_epochs_thread[i] = 0;
        write_epochs_timestamp[i] = 0;
    }
    
}

int detect(Event* e) {
    int is_race = 0;
    int Ct_t = read_clock(thread_clk[e->thread], e->thread);
    switch (e->type)
    {
        case ACQUIRE:
            join(thread_clk[e->thread], lock_clk[e->lock]);
            break;
        case RELEASE:
            monotone_copy(lock_clk[e->lock], thread_clk[e->thread]);
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
            if(!is_read_epoch || 
               read_epochs_thread[e->var] != e->thread || 
               vc_read_clock(read_epochs_timestamp[e->var], e->thread) != Ct_t) {
                if(is_read_epoch && vc_read_clock(read_epochs_timestamp[e->var], read_epochs_thread[e->var]) <= read_clock(thread_clk[e->thread], read_epochs_thread[e->var])
                   && write_epochs_timestamp[e->var] <= read_clock(thread_clk[e->thread], write_epochs_thread[e->var])) {
                    read_epochs_thread[e->var] = e->thread;
                    vc_write_clock(read_epochs_timestamp[e->var], e->thread, Ct_t);
                }
                else if(write_epochs_timestamp[e->var] <= read_clock(thread_clk[e->thread], write_epochs_thread[e->var])) {
                    is_read_epoch = 0;
                    vc_write_clock(read_epochs_timestamp[e->var], e->thread, Ct_t);
                }
                else {
                    is_race = 1;
                }
            }
            break;
        case WRITE:
            if(write_epochs_thread[e->var] != e->thread || 
               write_epochs_timestamp[e->var] != Ct_t) {
                int race_with_write = 0;
                int race_with_read = 0;
                if(write_epochs_timestamp[e->var] > read_clock(thread_clk[e->thread], write_epochs_thread[e->var])) {
                    race_with_write = 1;
                }
                if(!race_with_write) {
                    if(is_read_epoch && vc_read_clock(read_epochs_timestamp[e->var], read_epochs_thread[e->var]) > read_clock(thread_clk[e->thread], read_epochs_thread[e->var])) {
                        race_with_read = 1;
                    }
                    else if(!is_read_epoch){
                        for(int i = 0; i < MAX_THREADS; i++) {
                            if(vc_read_clock(read_epochs_timestamp[e->var], i) > read_clock(thread_clk[e->thread], i)) {
                                race_with_read = 1;
                            }
                        }
                    }
                }
                if(!race_with_read && !race_with_write) {
                    write_epochs_thread[e->var] = e->thread;
                    write_epochs_timestamp[e->var] = Ct_t;
                    if(!is_read_epoch) {
                        is_read_epoch = 1;
                        read_epochs_thread[e->var] = 0;
                        for(int i = 0; i < MAX_THREADS; i++) {
                            vc_write_clock(read_epochs_timestamp[e->var], i, 0);
                        }
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