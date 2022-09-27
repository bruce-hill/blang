#include <assert.h>
#include <bp/match.h>
#include <bp/pattern.h>
#include <bp/printmatch.h>
#include <ctype.h>
#include <err.h>
#include <gc.h>
#include <gc/cord.h>
#include <intern.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>
#include <time.h>

#include "types.h"

static const int64_t INT_NIL = 0x7FFFFFFFFFFFFFFF;

#define RETURN_FMT(fmt, ...) do { char *ret = NULL; int status = asprintf(&ret, fmt, __VA_ARGS__); if (status < 0) err(1, "string formatting failed"); const char *tmp = intern_str(ret); free(ret); return tmp; } while(0)
#define CLAMP(x, lo, hi) MIN(hi, MAX(x,lo))

const char *bl_string(const char *s) { return intern_str(s); }
const char *bl_tostring_int(int64_t i) { RETURN_FMT("%ld", i); }
const char *bl_tostring_int32(int32_t i) { RETURN_FMT("%d", i); }
const char *bl_tostring_int16(int16_t i) { RETURN_FMT("%d", i); }
const char *bl_tostring_int8(int8_t i) { RETURN_FMT("%d", i); }
const char *bl_tostring_hex(int64_t i) { RETURN_FMT("0x%lX", i); }
const char *bl_tostring_char(int64_t c) { RETURN_FMT("%c", (char)c); }
const char *bl_tostring_float(double f) { RETURN_FMT("%g", f); }
const char *bl_tostring_float32(float f) { RETURN_FMT("%g", f); }
const char *bl_tostring_percent(double f) { RETURN_FMT("%g%%", f*100.0); }
const char *bl_tostring_bool(int64_t b) { return intern_str(b ? "yes" : "no"); }
const char *bl_tostring_nil(void) { return intern_str("nil"); }
const char *bl_tostring_range(range_t *r) {
    if (r->first < 99999999 && r->last > 99999999)
        return intern_str("..");
    else if (r->first < 99999999)
        RETURN_FMT("..%ld", r->last);
    else if (r->last > 99999999 && r->next != r->first+1)
        RETURN_FMT("%ld,%ld..", r->first, r->next);
    else if (r->last > 99999999)
        RETURN_FMT("%ld..", r->first);
    else if (r->last > r->first ? (r->next == r->first+1) : (r->next == r->first-1))
        RETURN_FMT("%ld..%ld", r->first, r->last);
    else
        RETURN_FMT("%ld,%ld..%ld", r->first, r->next, r->last);
}
const char *bl_tostring_time(const char *fmt, int64_t seconds)
{
    size_t strftime(char *restrict s, size_t max,
                    const char *restrict format,
                    const struct tm *restrict tm);
    time_t t = seconds;
    struct tm tm;
    localtime_r(&t, &tm);
    char buf[128];
    strftime(buf, 127, fmt, &tm);
    return intern_str(buf);
}

// const char *bl_string_join(int64_t count, char **strings, char *sep) {
//     if (!strings) return NULL;
//     CORD buf = CORD_EMPTY;
//     size_t seplen = sep ? strlen(sep) : 0;
//     for (int64_t i = 0; i < count; i++) {
//         char *str = strings[i];
//         if (!str) str = "(nil)";
//         buf = CORD_cat(buf, str);
//         if (sep && i < count - 1)
//             buf = CORD_cat_char_star(buf, sep, seplen);
//     }
//     return bl_string(CORD_to_const_char_star(buf));
// }

// const char *bl_string_list_join(list_t *list, char *sep) {
//     return bl_string_join(list->len, (char**)list->items, sep);
// }

const char *bl_string_append_int(char *s, int64_t i) { RETURN_FMT("%s%ld", s, i); }
const char *bl_string_append_float(char *s, double f) { RETURN_FMT("%s%g", s, f); }
const char *bl_string_append_char(char *s, int64_t c) { RETURN_FMT("%s%c", s, (char)c); }
const char *bl_string_append_bool(char *s, int64_t b) { RETURN_FMT("%s%s", s, b ? "yes" : "no"); }
const char *bl_string_append_range(char *s, range_t *r) {
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
const char *bl_string_append_string(char *a, char *b) { RETURN_FMT("%s%s", a, b); }

const char *bl_string_slice(const char *s, range_t *r) {
    int64_t step = r->next - r->first;
    if (step == 0) return intern_str("");

    int64_t len = (int64_t)strlen(s);
    int64_t first = CLAMP(r->first-1, 0, len-1), last = CLAMP(r->last-1, 0, len-1);
    int64_t slice_len = 0;
    for (int64_t i = first; step > 0 ? i <= last : i >= last; i += step)
        ++slice_len;
    char *buf = calloc(slice_len+1, 1);
    assert(buf);
    for (int64_t i = first, b_i = 0; step > 0 ? i <= last : i >= last; i += step)
        buf[b_i++] = s[i];
    const char *ret = intern_str(buf);
    free(buf);
    return ret;
}

bool bl_string_starts_with(const char *s, const char *prefix) {
    while (*prefix) {
        if (*prefix++ != *s++)
            return false;
    }
    return true;
}

bool bl_string_ends_with(const char *s, const char *suffix) {
    size_t s_len = strlen(s);
    size_t suffix_len = strlen(suffix);
    if (suffix_len > s_len) return false;
    return memcmp(s+(s_len-suffix_len), suffix, suffix_len) == 0;
}

const char *bl_string_upper(const char *s) {
    char *s2 = strdup(s);
    for (char *p = s2; *p; p++)
        *p = toupper(*p);
    const char *ret = intern_str(s2);
    free(s2);
    return ret;
}

const char *bl_string_lower(const char *s) {
    char *s2 = strdup(s);
    for (char *p = s2; *p; p++)
        *p = tolower(*p);
    const char *ret = intern_str(s2);
    free(s2);
    return ret;
}

const char *bl_string_capitalized(const char *s) {
    if (!isalpha(s[0]) || isupper(s[0]))
        return s;
    char *s2 = strdup(s);
    s2[0] = toupper(s2[0]);
    const char *ret = intern_str(s2);
    free(s2);
    return ret;
}

const char *bl_string_titlecased(const char *s) {
    char *s2 = strdup(s);
    bool should_capitalize = true;
    for (char *p = s2; *p; p++) {
        if (isalpha(*p)) {
            if (should_capitalize) {
                *p = toupper(*p);
                should_capitalize = false;
            } else {
                *p = tolower(*p);
            }
        } else {
            should_capitalize = true;
        }
    }
    const char *ret = intern_str(s2);
    free(s2);
    return ret;
}

int64_t bl_string_nth_char(const char *s, int64_t n) {
    --n;
    if (n < 0) return INT_NIL;
    int64_t len = (int64_t)strlen(s);
    if (n > len) return INT_NIL;
    return (int64_t)s[n];
}

const char *bl_string_repeat(const char *s, int64_t count) {
    if (count <= 0) return intern_str("");
    size_t len = strlen(s);
    char *buf = calloc(len*count + 1, 1);
    assert(buf);
    char *p = buf;
    for (int64_t i = 0; i < count; i++) {
        memcpy(p, s, len);
        p += len;
    }
    const char *ret = intern_str(buf);
    free(buf);
    return ret;
}

const char *bl_string_strip(const char *s, const char *strip_chars, int8_t strip_left, int8_t strip_right) {
    if (strip_chars == NULL) strip_chars = " \n\r\t";
    const char *start = s;
    if (strip_left)
        start += strspn(s, strip_chars);
    size_t len = strlen(start);
    if (strip_right) {
        while (strspn(start + len - 1, strip_chars))
            --len;
    }
    const char *buf = strndupa(start, len);
    return intern_str(buf);
}

const char *bl_string_replace(char *text, char *pat_text, char *rep_text, int64_t limit) {
    maybe_pat_t maybe_pat = bp_stringpattern(pat_text, pat_text + strlen(pat_text));
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
    if (limit == INT_NIL) limit = textlen + 1;
    if (limit > 0) {
        for (match_t *m = NULL; next_match(&m, text, &text[textlen], rep_pat, NULL, NULL, false); ) {
            fwrite(prev, sizeof(char), (size_t)(m->start - prev), out);
            fprint_match(out, text, m, NULL);
            prev = m->end;
            if (--limit == 0) {
                stop_matching(&m);
                break;
            }
        }
    }
    fwrite(prev, sizeof(char), (size_t)(&text[textlen] - prev) + 1, out);
    fflush(out);
    const char *replaced = buf ? intern_str(buf) : intern_str("");
    fclose(out);
    return replaced;
}

// const char *bl_string_match(char *text, char *pat_text) {
//     maybe_pat_t maybe_pat = bp_pattern(pat_text, pat_text + strlen(pat_text));
//     if (!maybe_pat.success) {
//         return intern_str("");
//     }

//     char *buf = NULL;
//     size_t size = 0;
//     FILE *out = open_memstream(&buf, &size);
//     size_t textlen = strlen(text);
//     pat_t *pat = maybe_pat.value.pat;
//     for (match_t *m = NULL; next_match(&m, text, &text[textlen], pat, NULL, NULL, false); ) {
//         fprint_match(out, text, m, NULL);
//         stop_matching(&m);
//         break;
//     }
//     fflush(out);
//     const char *match = buf ? intern_str(buf) : intern_str("");
//     fclose(out);
//     return match;
// }

bool bl_string_matches(char *text, char *pat_text) {
    maybe_pat_t maybe_pat = bp_stringpattern(pat_text, pat_text + strlen(pat_text));
    if (!maybe_pat.success) {
        return intern_str("");
    }

    size_t textlen = strlen(text);
    pat_t *pat = maybe_pat.value.pat;
    match_t *m = NULL;
    if (next_match(&m, text, &text[textlen], pat, NULL, NULL, false)) {
        stop_matching(&m);
        return true;
    } else {
        return false;
    }
}

const char *bl_ask(char *prompt) {
    printf("%s", prompt);
    char *line = NULL;
    size_t capacity = 0;
    ssize_t len = getline(&line, &capacity, stdin);
    if (len < 0 || !line)
        return NULL;
    if (len > 1 && line[len-1] == '\n')
        line[--len] = '\0';
    const char *ret = intern_str(line);
    free(line);
    return ret;
}

const char *bl_system(char *cmd) {
    FILE *f = popen(cmd, "r");
    char buffer[256];
    size_t chread;
    /* String to store entire command contents in */
    size_t comalloc = 256;
    size_t comlen = 0;
    char *comout = malloc(comalloc);
 
    /* Use fread so binary data is dealt with correctly */
    while ((chread = fread(buffer, 1, sizeof(buffer), f)) > 0) {
        if (comlen + chread >= comalloc) {
            comalloc *= 2;
            comout = realloc(comout, comalloc);
        }
        memmove(comout + comlen, buffer, chread);
        comlen += chread;
    }
 
    comout[strlen(comout)-1] = '\0';
    const char *ret = bl_string(comout);
    free(comout);
    pclose(f);
    return ret;
}
