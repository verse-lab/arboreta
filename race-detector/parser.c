#include <stdio.h>
#include <regex.h>
#include "parser.h"

// @TYPE(Thread, VAR/LOCK/THR) LOC

char variables[MAX_VARS][1024];
char locks[MAX_VARS][1024];

void parse(char* buf, Event* e) {
    
}