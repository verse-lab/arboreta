#include <stdio.h>
#include "detector.h"

int thread_clk[MAX_THREADS][MAX_THREADS];
int read_clk[MAX_VARS][MAX_THREADS];
int write_clk[MAX_VARS][MAX_THREADS];
int lock_clk[MAX_LOCKS][MAX_THREADS];

void init() {
    for(int i = 0; i < MAX_THREADS; i++) {
        for(int j = 0; j < MAX_THREADS; j++) {
            thread_clk[i][j] = 0;
        }
    }
    for(int i = 0; i < MAX_VARS; i++) {
        for(int j = 0; j < MAX_THREADS; j++) {
            read_clk[i][j] = 0;
            write_clk[i][j] = 0;
        }
    }
    for(int i = 0; i < MAX_LOCKS; i++) {
        for(int j = 0; j < MAX_THREADS; j++) {
            lock_clk[i][j] = 0;
        }
    }
}

// clk1 = clk1 \join clk2
void join(int* clk1, int* clk2) {
    for(int i = 0; i < MAX_THREADS; i++) {
        clk1[i] = (clk1[i] > clk2[i]) ? clk1[i] : clk2[i];
    }
}

// clk := clk[index := clk[index] + 1]
void increment(int* clk, int index) {
    clk[index] += 1;
}

// clk1 := clk2
void copy(int* clk1, int* clk2) {
    for(int i = 0; i < MAX_THREADS; i++) {
        clk1[i] = clk2[i];
    }
}

// clk1 \less_than clk2
int less_than(int* clk1, int* clk2) {
    int le = 1;
    for(int i = 0; i < MAX_THREADS; i++) {
        if(clk1[i] > clk2[i]) {
            le = 0;
            break;
        }
    }
    return le;
}

int detect(Event* e) {
    int is_race = 0;
    switch (e -> type)
    {
        case ACQUIRE:
            join(thread_clk[e -> thread], lock_clk[e -> lock]);
            break;
        case RELEASE:
            increment(thread_clk[e -> thread], e -> thread);
            copy(lock_clk[e -> lock], thread_clk[e -> thread]);
            break;
        case FORK:
            increment(thread_clk[e -> thread], e -> thread);
            join(thread_clk[e -> thr2], thread_clk[e -> thread]);
            break;
        case JOIN:
            increment(thread_clk[e -> thr2], e -> thr2);
            join(thread_clk[e -> thread], thread_clk[e -> thr2]);
            break;
        case READ:
            if(less_than(write_clk[e -> var], thread_clk[e -> thread])) {
                // think of this
                read_clk[e -> var][e -> thread] = thread_clk[e -> thread][e -> thread];
            }
            else if(read_clk[e -> var][e -> thread] != thread_clk[e -> thread][e -> thread]) {
                is_race = 1;
            }
            break;
        case WRITE:
            if(less_than(write_clk[e -> var], thread_clk[e -> thread])
                && less_than(read_clk[e -> var], thread_clk[e -> thread])) {
                // think of this
                write_clk[e -> var][e -> thread] = thread_clk[e -> thread][e -> thread];
            }
            else if(write_clk[e -> var][e -> thread] != thread_clk[e -> thread][e -> thread]) {
                is_race = 1;
            }
            break;
        default:
            break;
    }
    return is_race;
}