#ifndef _HEADER_DATA_STRUCTURE_H
#define _HEADER_DATA_STRUCTURE_H

#define MAX_THREADS 100
#define MAX_VARS    1024
#define MAX_LOCKS   1024

#define READ        0
#define WRITE       1
#define ACQUIRE     2
#define RELEASE     3
#define FORK        4
#define JOIN        5
#define OTHER       6

typedef struct event {
    int type;
    int thread;
    int var;
    int lock;
    int thr2;
} Event;


#endif