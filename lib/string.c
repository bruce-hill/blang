#include <bhash.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>

#include "types.h"

#define RETURN_FMT(fmt, ...) do { char *ret; asprintf(&ret, fmt, __VA_ARGS__); return intern_str_transfer(ret); } while(0)

char *blang_string(char *s) { return intern_str(s); }
char *blang_tostring_int(long i) { RETURN_FMT("%ld", i); }
char *blang_tostring_float(double f) { RETURN_FMT("%g", f); }
char *blang_tostring_bool(long b) { return intern_str(b ? "yes" : "no"); }
char *blang_tostring_nil(void) { return intern_str("nil"); }

char *blang_string_append_int(char *s, long i) { RETURN_FMT("%s%ld", s, i); }
char *blang_string_append_float(char *s, double f) { RETURN_FMT("%s%g", s, f); }
char *blang_string_append_char(char *s, long c) { RETURN_FMT("%s%c", s, (char)c); }
char *blang_string_append_bool(char *s, long b) { RETURN_FMT("%s%s", s, b ? "yes" : "no"); }
char *blang_string_append_range(char *s, Range *r) {
    RETURN_FMT("%s[%ld,%ld..%ld]", s, r->first, r->next, r->last);
}

char *blang_string_concat(char *a, char *b) { RETURN_FMT("%s%s", a, b); }

char *blang_string_slice(char *s, Range *r) {
    long step = r->next - r->first;
    if (step == 0) return intern_str("");

    long first = r->first-1, last = r->last-1;
    long len = (long)strlen(s);
    long slice_len;
    if (step > 0) {
        first = MAX(first, 0);
        last = MIN(last, len-1);
        slice_len = MAX(1 + (last - first), len - first);
    } else {
        last = MAX(last, 0);
        first = MIN(first, len-1);
        slice_len = MAX(1 + (first - last), len - last);
    }
    char *buf = calloc(slice_len+1, 1);
    for (long i = first, b_i = 0; step > 0 ? i <= last : i >= last; i += step)
        buf[b_i++] = s[i];
    return intern_str_transfer(buf);
}

char *blang_string_upper(char *s) {
    char *s2 = strdup(s);
    for (int i = 0; s2[i]; i++)
        s2[i] = toupper(s2[i]);
    return intern_str_transfer(s2);
}

char *blang_string_lower(char *s) {
    char *s2 = strdup(s);
    for (int i = 0; s2[i]; i++)
        s2[i] = tolower(s2[i]);
    return intern_str_transfer(s2);
}

long blang_string_nth_char(char *s, long n) {
    --n;
    if (n < 0) return -1;
    long len = (long)strlen(s);
    if (n > len) return -1;
    return s[n];
}
