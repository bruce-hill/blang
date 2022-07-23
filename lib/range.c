#include <stdint.h>

#include "types.h"
#include "gc.h"

int64_t RANGE_MIN = -999999999999999999;
int64_t RANGE_MAX = +999999999999999999;

range_t *range_new(int64_t first, int64_t next, int64_t last) {
    range_t *r = gc_alloc(sizeof(range_t));
    r->first = first;
    r->next = next;
    if (next != first && last != first) {
        int64_t len = (last - first) / (next - first);
        last = first + len * (next - first);
    }
    r->last = last;
    return r;
}

range_t *range_new_first_last(int64_t first, int64_t last) {
    range_t *r = gc_alloc(sizeof(range_t));
    r->first = first;
    r->next = first <= last ? first+1 : first-1;
    r->last = last;
    return r;
}

range_t *range_new_first_next(int64_t first, int64_t next) {
    range_t *r = gc_alloc(sizeof(range_t));
    r->first = first;
    r->next = next;
    r->last = next >= first ? RANGE_MAX : RANGE_MIN;
    return r;
}

int64_t range_len(range_t *r) {
    int64_t len = (r->last - r->first) / (r->next - r->first);
    return (len < 0) ? 0 : len + 1;
}

int64_t range_nth(range_t *r, int64_t n) {
    int64_t step = r->next - r->first;
    return r->first + (n-1)*step;
}

int64_t range_step(range_t *r) {
    return r->next - r->first;
}

range_t *range_backwards(range_t *src) {
    int64_t step = src->next - src->first;
    return range_new(src->last, src->last - step, src->first);
}

list_t *bl_list_slice(list_t *list, range_t *r, size_t list_item_size, bool allow_aliasing) {
    list_t *slice = gc_alloc(sizeof(list_t));
    int64_t first = r->first;
    int64_t step = r->next - r->first;
    if (step == 0) return slice;
    // printf("step: %ld\n", step);
    int64_t last = r->last;
    if (step > 0) {
        if (first > list->len) return slice;
        if (first < 1) {
            first = first % step;
            if (first < 1) first += step;
        }
        if (last > list->len) last = list->len;
        if (last < first) return slice;
    } else {
        if (first < 1) return slice;
        if (first > list->len) {
            first = list->len - (list->len % -step) + (first % -step);
            if (first > list->len) first += step;
        }
        if (last < 1) last = 1;
        if (last > first) return slice;
    }
    int64_t len = ((last+step) - first) / step;
    if (len <= 0) len = 0;
    slice->len = len;

    if (step == 1 && allow_aliasing) {
        slice->items = &list->items[first-1];
    } else if (len > 0) {
        void *p = gc_alloc(len * list_item_size);
        slice->items = p;
        void *src_items = list->items;
        int64_t actual_len = 0;
        for (int64_t i = first; step > 0 ? (i <= last) : (i >= last); i += step) {
            actual_len += 1;
            p = mempcpy(p, src_items + (i - 1)*list_item_size, list_item_size);
        }
    }
    return slice;
}
