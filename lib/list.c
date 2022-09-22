#include <stdint.h>
#include <err.h>
#include "gc.h"
#include "types.h"

static const int64_t INT_NIL = 0x7FFFFFFFFFFFFFFF;

void list_insert_all(list_t *list, size_t item_size, int64_t index, list_t *other, const char *err_fmt) {
    if (index == INT_NIL) index = list->len + 1;
    else if (__builtin_expect((index < 1) | (index > list->len + 1), 0))
        errx(1, err_fmt, index);
    char *old_items = list->items.i8;
    list->items.i8 = gc_alloc(item_size * (list->len + other->len));
    memcpy(list->items.i8, old_items, item_size*(index-1));
    memcpy(list->items.i8 + (index-1)*item_size, other->items.i8, other->len*item_size);
    memcpy(list->items.i8 + (index-1 + other->len)*item_size, old_items+item_size*(index-1), item_size*(list->len - (index-1)));
    list->len += other->len;
}

void list_insert(list_t *list, size_t item_size, int64_t index, int64_t item, const char *err_fmt) {
    if (index == INT_NIL) index = list->len + 1;
    else if (__builtin_expect((index < 1) | (index > list->len + 1), 0))
        errx(1, err_fmt, index);
    char *old_items = list->items.i8;
    list->items.i8 = gc_alloc(item_size * (list->len + 1));
    memcpy(list->items.i8, old_items, item_size*(index-1));
    switch (item_size) {
        case 8: list->items.i64[index-1] = *((int64_t*)&item); break;
        case 4: list->items.i32[index-1] = *((int32_t*)&item); break;
        case 2: list->items.i16[index-1] = *((int16_t*)&item); break;
        case 1: list->items.i8[index-1]  = *((int8_t*)&item); break;
        default: break;
    }
    memcpy(list->items.i8+item_size*index, old_items+item_size*(index-1), item_size*(list->len - (index-1)));
    list->len += 1;
}

void list_remove(list_t *list, size_t item_size, int64_t first, int64_t last) {
    if (last == INT_NIL) last = first;

    if (first > list->len) return;
    if (first < 1) first = 1;
    if (last > list->len) last = list->len;
    if (last < first) return;

    int64_t len = last - first + 1;
    if (len <= 0) len = 0;

    memmove(&list->items.i8[item_size*(first-1)], &list->items.i8[item_size*last], item_size * len);
    list->len -= len;
    if (list->len == 0) list->items.i8 = NULL;
}

bool list_equal(list_t *a, list_t *b, size_t item_size) {
    return a == b || ((a->len | b->len) == 0) || (a->len == b->len && memcmp(a->items.i8, b->items.i8, a->len*item_size));
}

list_t *list_copy(list_t *l, size_t item_size) {
    list_t *copy = gc_alloc(sizeof(list_t));
    copy->len = l->len;
    if (l->len > 0) {
        copy->items.i8 = gc_alloc(item_size*l->len);
        memcpy(copy->items.i8, l->items.i8, item_size*l->len);
    }
    return copy;
}

void list_clear(list_t *l) {
    l->len = 0;
    l->items.i8 = NULL;
}

list_t *list_slice(list_t *list, range_t *r, size_t list_item_size, bool allow_aliasing) {
    list_t *slice = gc_alloc(sizeof(list_t));
    int64_t first = r->first;
    int64_t step = r->next - r->first;
    if (step == 0) return slice;
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
        slice->items.i8 = list->items.i8 + (first-1)*list_item_size;
    } else if (len > 0) {
        void *p = gc_alloc(len * list_item_size);
        slice->items.i8 = p;
        void *src_items = list->items.i8;
        if (step == 1) {
            memcpy(slice->items.i8, &list->items.i8[(first-1)*list_item_size], len * list_item_size);
        } else {
            int64_t actual_len = 0;
            for (int64_t i = first; step > 0 ? (i <= last) : (i >= last); i += step) {
                actual_len += 1;
                p = mempcpy(p, src_items + (i - 1)*list_item_size, list_item_size);
            }
            slice->len = actual_len;
        }
    }
    return slice;
}
