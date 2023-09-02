#include <stdlib.h>
#include <stdio.h>
#include "parser.h"
#include "detector.h"
#include "data_structure.h"


int main(int argc, char* argv[]) {
    if(argc != 1) {
        return 0;
    }

    FILE* trace = fopen(argv[0], "r");
    char buf[1024];

    Event e = {};
    int is_race = 0;
    long count = 0;

    while (fgets(buf, sizeof(buf), trace) != NULL)
    {
        count++;
        parse(buf, &e);
        if(detect(&e)) {
            is_race = 1;
            break;
        }
    }
    fclose(trace);

    if(is_race) {
        printf("RACE FOUND after %ld events.\n", count);
    }
    else {
        printf("NO RACE.\n");
    }
    
    return 0;
}