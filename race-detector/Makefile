CC=gcc
CFLAGS = -c

OBJECTS = engine.o parser.o vectorClock.o detector.o

all: prog

prog: $(OBJECTS)
	$(CC) $(OBJECTS) -o Engine

%.o: %.c
	$(CC) $(CFLAGS) $<

.PONY: clean
clean:
	rm -rf Engine *.o