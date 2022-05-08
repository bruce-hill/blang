#include <stdio.h>

typedef struct { long first, next, last; } Range;

void init_range3(Range *r, long first, long next, long last) {
    r->first = first;
    r->next = next;
    if (next != first && last != first) {
        long len = (last - first) / (next - first);
        last = first + len * (next - first);
    }
    r->last = last;
}

void init_range2(Range *r, long first, long last) {
    r->first = first;
    r->next = first <= last ? first+1 : first-1;
    r->last = last;
}

long range_len(Range *r) {
    long len = (r->last - r->first) / (r->next - r->first);
    return (len < 0) ? 0 : len + 1;
}

long range_nth(Range *r, long n) {
    long step = r->next - r->first;
    return r->first + (n-1)*step;
}

long range_step(Range *r) {
    return r->next - r->first;
}

void range_backwards(Range *dest, Range *src) {
    long step = src->next - src->first;
    dest->first = src->last;
    dest->next = dest->first - step;
    dest->last = src->first;
}

int print_range(Range *r) {
    return printf("[%ld,%ld..%ld]", r->first, r->next, r->last);
}
