#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>

#include "types.h"
#include "gc.h"

list_t *bl_list_new(int64_t nitems, int64_t *items) {
    list_t *list = gc_alloc(sizeof(list_t));
    if (nitems > 0) {
        list->items = gc_alloc(nitems*sizeof(int64_t));
        memcpy(list->items, items, sizeof(int64_t)*nitems);
        list->len = nitems;
    }
    return list;
}

void bl_list_free(list_t *list) {
    if (list->items) {
        gc_free(list->items);
        list->items = NULL;
    }
    gc_free(list);
}

void bl_list_append(list_t *list, int64_t item) {
    list->items = gc_realloc(list->items, (list->len+1)*sizeof(int64_t));
    list->items[list->len++] = item;
}

list_t *bl_list_concat(list_t *a, list_t *b) {
    list_t *list = gc_alloc(sizeof(list_t));
    if (a->len > 0 || b->len > 0) {
        list->items = gc_alloc((a->len + b->len)*sizeof(int64_t));
        if (a->len > 0)
            memcpy(list->items, a->items, sizeof(int64_t)*a->len);
        if (b->len > 0)
            memcpy(&list->items[a->len], b->items, sizeof(int64_t)*b->len);
    }
    return list;
}

void bl_list_remove(list_t *list, int64_t i) {
    if (i < 1 || i > list->len) return;
    if (i < list->len)
        memmove(&list->items[i-1], &list->items[i], list->len - i);
    --list->len;
}

int64_t bl_list_len(list_t *list) {
    return list->len;
}

int64_t bl_list_nth(list_t *list, int64_t i) {
    if (i < 1 || i > list->len) return 0;
    return list->items[i-1];
}

void bl_list_set_nth(list_t *list, int64_t i, int64_t val) {
    if (i < 1 || i > list->len) return;
    list->items[i-1] = val;
}

list_t *bl_list_slice(list_t *list, int64_t first, int64_t next, int64_t last) {
    int64_t step = next - first;
    int64_t len = list->len;
    if (step == 0 || (first < 1 && last < 1) || (first > len && last > len))
        return bl_list_new(0, NULL);

    first = MAX(1, MIN(len, first));
    last = MAX(1, MIN(len, last));

    int64_t slice_len = 0;
    for (int64_t i = first; step > 0 ? i <= last : i >= last; i += step)
        ++slice_len;

    if (step == 1)
        return bl_list_new(slice_len, list->items);

    list_t *slice = gc_alloc(sizeof(list_t));
    list->len = slice_len;
    list->items = gc_alloc(slice_len*sizeof(int64_t));
    for (int64_t src = first, dest = 0; step > 0 ? src <= last : src >= last; src += step)
        slice->items[dest++] = list->items[src];
    return slice;
}

list_t *bl_list_slice_range(list_t *list, range_t *r) {
    return bl_list_slice(list, r->first, r->next, r->last);
}
