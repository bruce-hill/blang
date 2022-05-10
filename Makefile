CC=cc
PREFIX=/usr/local
CFLAGS=-std=c99 -Werror -D_XOPEN_SOURCE=700 -D_POSIX_C_SOURCE=200809L -flto -D_GNU_SOURCE
CWARN=-Wall -Wextra
EXTRA=
G=-ggdb
O=-O3
LIBS=-lm -lbhash
ALL_FLAGS=$(CFLAGS) $(EXTRA) $(CWARN) $(G) $(O) $(LIBS)

CFILES=lib/range.c lib/string.c lib/reduce.c lib/list.c lib/array.c lib/math.c
OBJFILES=$(CFILES:.c=.o)

all: $(OBJFILES)

%.o: %.c
	$(CC) -c $(ALL_FLAGS) -o $@ $<

clean:
	rm -f $(OBJFILES)

test: all
	./blang test/*.bl

.PHONY: all clean test
