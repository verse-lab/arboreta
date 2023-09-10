#include <stdio.h>
#include "detector.h"
#include "treeclock_ndt.h"
#include "vectorclock.h"

// #define _DEBUG

// #define CLOCK_T                 TreeClock_T
// #define init_tid                tc_init_tid
// #define init                    tc_init
// #define increment_clock         tc_increment_clock
// #define read_clock              tc_read_clock
// #define write_clock             tc_write_clock
// #define join                    tc_join
// #define is_less_than_or_equal   tc_is_less_than_or_equal
// #define monotone_copy           tc_monotone_copy

#define CLOCK_T                 VectorClock_T
#define init_tid                vc_init_tid
#define init                    vc_init
#define increment_clock         vc_increment_clock
#define read_clock              vc_read_clock
#define write_clock             vc_write_clock
#define join                    vc_join
#define is_less_than_or_equal   vc_is_less_than_or_equal
#define monotone_copy           vc_monotone_copy

CLOCK_T thread_clk[MAX_THREADS];
CLOCK_T read_clk[MAX_VARS];
CLOCK_T write_clk[MAX_VARS];
CLOCK_T lock_clk[MAX_LOCKS];
int a = 0;

#ifdef _DEBUG
void print_clk(CLOCK_T clk) {
    for(int i = 0; i < MAX_THREADS; i++) {
        printf("%d ", (clk->clocks)[i]);
    }
    printf("\n");
}
#endif

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
            if(is_less_than_or_equal(write_clk[e->var], thread_clk[e->thread])) {
                join(read_clk[e->var], thread_clk[e->thread]);
            }
            else if(read_clock(read_clk[e->var], e->thread) != read_clock(thread_clk[e->thread], e->thread)) {
                is_race = 1;
            }
            break;
        case WRITE:
            #ifdef _DEBUG
            printf("write\n");
            print_clk(write_clk[e->var]);
            print_clk(thread_clk[e->thread]);
            printf("lessw: %d\n", is_less_than_or_equal(write_clk[e->var], thread_clk[e->thread]));
            printf("lessr: %d\n", is_less_than_or_equal(read_clk[e->var], thread_clk[e->thread]));
            #endif
            
            if(is_less_than_or_equal(write_clk[e->var], thread_clk[e->thread])
                && is_less_than_or_equal(read_clk[e->var], thread_clk[e->thread])) {
                join(write_clk[e->var], thread_clk[e->thread]);
            }
            else if(read_clock(write_clk[e->var], e->thread) != read_clock(thread_clk[e->thread], e->thread)) {
                is_race = 1;
            }
            break;
        default:
            break;
    }
    #ifdef _DEBUG
    for(int i = 0; i < MAX_THREADS; i++) {
        print_clk(thread_clk[i]);
    }
    for(int i = 0; i < MAX_THREADS; i++) {
        print_clk(read_clk[i]);
    }
    for(int i = 0; i < MAX_THREADS; i++) {
        print_clk(write_clk[i]);
    }
    for(int i = 0; i < MAX_THREADS; i++) {
        print_clk(lock_clk[i]);
    }
    #endif
    return is_race;
}