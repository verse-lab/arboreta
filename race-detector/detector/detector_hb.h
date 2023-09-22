#ifndef _HEADER_DETECTOR_HB_H
#define _HEADER_DETECTOR_HB_H
#include "data_structure.h"

void init_detector(int tnum, int vnum, int lnum);
void free_detector();
int detect(Event* e);

#endif
