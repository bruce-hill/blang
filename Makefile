CC=cc
PREFIX=/usr/local
CFLAGS=-std=c99 -Werror -D_XOPEN_SOURCE=700 -D_POSIX_C_SOURCE=200809L -flto -D_GNU_SOURCE -fPIC
CWARN=-Wall -Wextra
EXTRA=
G=-ggdb
O=-O0
LIBS=-lm -lbhash -ldl
ALL_FLAGS=$(CFLAGS) $(EXTRA) $(CWARN) $(G) $(O) $(LIBS)

CFILES=lib/range.c lib/string.c lib/reduce.c lib/list.c lib/math.c lib/gc.c lib/use.c
OBJFILES=$(CFILES:.c=.o)

all: getsym $(OBJFILES) libblang.so libintern.so

libblang.so: $(OBJFILES)
	cc -shared -Wl,-soname,libblang.so -o $@ $^

libintern.so: gc_intern/stringintern.c
	cc -shared -Wl,-soname,libintern.so -o $@ $^ -lgc

%.o: %.bl
	./blang -cc lib/builtins.bl

%.o: %.c
	$(CC) -c $(ALL_FLAGS) -o $@ $<

clean:
	rm -f $(OBJFILES)

test: all
	for f in test/*.bl; do printf '\x1b[33;1;4m%s\x1b[m\n' "$$f" && ./blang $$f || exit 1; done
	@printf '\n\x1b[42;30m All tests passed! \x1b[m\n\n'

.PHONY: all clean test
