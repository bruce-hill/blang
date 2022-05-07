#include <string.h>
#include <stdio.h>
#include <bhash.h>
#include <ctype.h>

#define RETURN_FMT(fmt, ...) do { char *ret; asprintf(&ret, fmt, __VA_ARGS__); return intern_str_transfer(ret); } while(0)

char *blang_tostring_int(long i) { RETURN_FMT("%ld", i); }
char *blang_tostring_float(double f) { RETURN_FMT("%f", f); }
char *blang_tostring_bool(long b) { return intern_str(b ? "yes" : "no"); }
char *blang_tostring_nil(void) { return intern_str("nil"); }

char *blang_string_concat(char *a, char *b) { RETURN_FMT("%s%s", a, b); }

char *blang_string_slice(char *s, long first, long last) {
    long len = (long)strlen(s);
    if (len == 0) return intern_str("");

    if (first < 1) first = 1;
    else if (first > len) first = len;

    if (last < 1) last = 1;
    else if (last > len) last = len;

    if (last < first) return intern_str("");

    long slice_len = 1 + (last - first);
    RETURN_FMT("%.*s", (int)slice_len, &s[first-1]);
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
