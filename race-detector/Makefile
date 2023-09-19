CC=gcc
CFLAGS = -c

OBJECTS = treeclock_ndt.o treeclock_ptr.o vectorclock.o
OBJ_HB 	= detector_hb.o
OBJ_FT	= detector_ft.o

all: hb

hb: $(OBJECTS) $(OBJ_HB)
	rm -rf Engine_hb.so output
	$(CC) $(OBJECTS) $(OBJ_HB) -shared -o Engine_hb.so
	mkdir output
	mv *.o output

ft: $(OBJECTS) $(OBJ_FT)
	rm -rf Engine_ft.so output
	$(CC) $(OBJECTS) $(OBJ_FT) -shared -o Engine_ft.so
	mkdir output
	mv *.o output

%.o: detector/%.c
	$(CC) $(CFLAGS) $< 

.PONY: clean
clean:
	rm -rf Engine_ft.so Engine_hb.so output