#include <bhash.h>
#include <bp/pattern.h>
#include <bp/match.h>
#include <bp/printmatch.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>

#include "types.h"
#include "util.h"

#define RETURN_FMT(fmt, ...) do { char *ret; asprintf(&ret, fmt, __VA_ARGS__); return intern_str_transfer(ret); } while(0)

char *bl_string(char *s) { return intern_str(s); }
char *bl_tostring_int(int64_t i) { RETURN_FMT("%ld", i); }
char *bl_tostring_float(double f) { RETURN_FMT("%g", f); }
char *bl_tostring_bool(int64_t b) { return intern_str(b ? "yes" : "no"); }
char *bl_tostring_nil(void) { return intern_str("nil"); }

char *bl_string_append_int(char *s, int64_t i) { RETURN_FMT("%s%ld", s, i); }
char *bl_string_append_float(char *s, double f) { RETURN_FMT("%s%g", s, f); }
char *bl_string_append_char(char *s, int64_t c) { RETURN_FMT("%s%c", s, (char)c); }
char *bl_string_append_bool(char *s, int64_t b) { RETURN_FMT("%s%s", s, b ? "yes" : "no"); }
char *bl_string_append_range(char *s, range_t *r) {
    if (r->first < 99999999 && r->last > 99999999)
        RETURN_FMT("%s..", s);
    else if (r->first < 99999999)
        RETURN_FMT("%s..%ld", s, r->last);
    else if (r->last > 99999999 && r->next != r->first+1)
        RETURN_FMT("%s%ld,%ld..", s, r->first, r->next);
    else if (r->last > 99999999)
        RETURN_FMT("%s%ld..", s, r->first);
    else if (r->last > r->first ? (r->next == r->first+1) : (r->next == r->first-1))
        RETURN_FMT("%s%ld..%ld", s, r->first, r->last);
    else
        RETURN_FMT("%s%ld,%ld..%ld", s, r->first, r->next, r->last);
}
char *bl_string_append_string(char *a, char *b) { RETURN_FMT("%s%s", a, b); }

char *bl_string_slice(char *s, range_t *r) {
    int64_t step = r->next - r->first;
    if (step == 0) return intern_str("");

    int64_t len = (int64_t)strlen(s);
    int64_t first = MAX(0, MIN(len-1, r->first-1)), last = MAX(0, MIN(len-1, r->last-1));
    int64_t slice_len = 0;
    for (int64_t i = first; step > 0 ? i <= last : i >= last; i += step)
        ++slice_len;
    char *buf = calloc2(slice_len+1, 1);
    for (int64_t i = first, b_i = 0; step > 0 ? i <= last : i >= last; i += step)
        buf[b_i++] = s[i];
    return intern_str_transfer(buf);
}

char *bl_string_upper(char *s) {
    char *s2 = strdup(s);
    for (int i = 0; s2[i]; i++)
        s2[i] = toupper(s2[i]);
    return intern_str_transfer(s2);
}

char *bl_string_lower(char *s) {
    char *s2 = strdup(s);
    for (int i = 0; s2[i]; i++)
        s2[i] = tolower(s2[i]);
    return intern_str_transfer(s2);
}

int64_t bl_string_nth_char(char *s, int64_t n) {
    --n;
    if (n < 0) return -1;
    int64_t len = (int64_t)strlen(s);
    if (n > len) return -1;
    return s[n];
}

char *bl_string_repeat(char *s, int64_t count) {
    if (count <= 0) return intern_str("");
    size_t len = strlen(s);
    char *buf = calloc2(len*count + 1, 1);
    char *p = buf;
    for (int64_t i = 0; i < count; i++) {
        memcpy(p, s, len);
        p += len;
    }
    return intern_str_transfer(buf);
}

char *bl_string_replace(char *text, char *pat_text, char *rep_text) {
    maybe_pat_t maybe_pat = bp_pattern(pat_text, pat_text + strlen(pat_text));
    if (!maybe_pat.success) {
        return text;
    }
    pat_t *pat = maybe_pat.value.pat;

    maybe_pat_t maybe_replacement = bp_replacement(pat, rep_text, rep_text + strlen(rep_text));
    if (!maybe_replacement.success) {
        return text;
    }

    char *buf = NULL;
    size_t size = 0;
    FILE *out = open_memstream(&buf, &size);
    const char *prev = text;
    pat_t *rep_pat = maybe_replacement.value.pat;
    size_t textlen = strlen(text);
    for (match_t *m = NULL; next_match(&m, text, &text[textlen], rep_pat, NULL, NULL, false); ) {
        fwrite(prev, sizeof(char), (size_t)(m->start - prev), out);
        fprint_match(out, text, m, NULL);
        prev = m->end;
    }
    fwrite(prev, sizeof(char), (size_t)(&text[textlen] - prev), out);
    fflush(out);
    char *replaced = intern_bytes(buf, size);
    fclose(out);
    return replaced;
}
