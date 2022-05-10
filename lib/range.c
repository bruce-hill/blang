#include <bhash.h>

#include "types.h"
#include "util.h"

long RANGE_MIN = -999999999999999999;
long RANGE_MAX = 999999999999999999;

range_t *range_new3(long first, long next, long last) {
    range_t *r = calloc2(1, sizeof(range_t));
    r->first = first;
    r->next = next;
    if (next != first && last != first) {
        long len = (last - first) / (next - first);
        last = first + len * (next - first);
    }
    r->last = last;
    return (range_t*)intern_bytes_transfer((char*)r, sizeof(range_t));
}

range_t *range_new2(long first, long last) {
    range_t *r = calloc2(1, sizeof(range_t));
    r->first = first;
    r->next = first <= last ? first+1 : first-1;
    r->last = last;
    return (range_t*)intern_bytes_transfer((char*)r, sizeof(range_t));
}

long range_len(range_t *r) {
    long len = (r->last - r->first) / (r->next - r->first);
    return (len < 0) ? 0 : len + 1;
}

long range_nth(range_t *r, long n) {
    long step = r->next - r->first;
    return r->first + (n-1)*step;
}

long range_step(range_t *r) {
    return r->next - r->first;
}

range_t *range_backwards(range_t *src) {
    long step = src->next - src->first;
    return range_new3(src->last, src->last - step, src->first);
}
