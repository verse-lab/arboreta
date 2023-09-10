CC=gcc
CFLAGS = -c

OBJECTS = treeclock_ndt.o vectorclock.o detector.o

all: prog

prog: $(OBJECTS)
	rm -rf Engine.so output
	$(CC) $(OBJECTS) -shared -o Engine.so
	mkdir output
	mv *.o output

%.o: detector/%.c
	$(CC) $(CFLAGS) $< 

.PONY: clean
clean:
	rm -rf Engine.so output