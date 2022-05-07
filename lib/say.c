#include <stdio.h>

void say_int(long i) { printf("%ld", i); }
void say_float(double f) { printf("%f", f); }
void say_bool(long b) { printf("%s", b ? "yes" : "no"); }
void say_nil(void) { printf("nil"); }
void say_string(char *s) { printf("%s", s); }
