// Purely functional lists
#include <bhash.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>

#include "types.h"
#include "util.h"

#define LIST_SIZE(n) (sizeof(list_t)+((n)-1)*sizeof(int64_t))

list_t *bl_empty_list(void) {
    static list_t *empty = NULL;
    if (empty == NULL) {
        size_t size = LIST_SIZE(0);
        empty = calloc2(1, size);
        empty->before = empty;
        empty->after = empty;
        empty = (list_t*)intern_bytes_transfer((void*)empty, size);
    }
    return empty;
}

int64_t bl_list_nth(list_t *list, int64_t i) {
    if (i < 1 || i > list->len) return 0;
    for (;;) {
        if (i <= list->before->len) {
            list = list->before;
        } else if (i <= (list->len - list->after->len)) {
            return list->items[i - list->before->len - 1];
        } else {
            i -= (list->len - list->after->len);
            list = list->after;
        }
    }
}

list_t *bl_list_coalesce(list_t *list) {
    list_t *empty = bl_empty_list();
    if (list->before == empty && list->after == empty)
        return list;
    size_t size = LIST_SIZE(list->len);
    list_t *coalesced = calloc2(1, size);
    coalesced->len = list->len;
    coalesced->before = empty;
    coalesced->after = empty;
    coalesced->depth = 0;
    for (int64_t i = 1; i <= list->len; i++)
        coalesced->items[i-1] = bl_list_nth(list, i);
    coalesced = (list_t*)intern_bytes_transfer((void*)coalesced, size);
    return coalesced;
}

list_t *bl_list_new(list_t *before, list_t *after, int64_t len, int64_t *items) {
    list_t *empty = bl_empty_list();
    if (len <= 0) return empty;
    if (before == NULL) before = empty;
    if (after == NULL) after = empty;
    int64_t nitems = len - (before->len + after->len);
    size_t size = LIST_SIZE(nitems);
    list_t *list = calloc2(1, size);
    list->before = before;
    list->after = after;
    list->len = len;
    list->depth = 1 + MAX(before->depth, after->depth);

    memcpy(list->items, items, nitems*sizeof(int64_t));
    if (1<<list->depth > 3*list->len) {
        list_t *tofree = list;
        list = bl_list_coalesce(list);
        if (tofree != list) free(tofree);
    } else {
        list = (list_t*)intern_bytes_transfer((void*)list, size);
    }
    return list;
}

list_t *bl_list_concat(list_t *a, list_t *b) {
    return bl_list_new(a, b, 0, NULL);
}

list_t *bl_list_append(list_t *list, int64_t item) {
    return bl_list_new(list, NULL, list->len+1, &item);
}

list_t *bl_list_prepend(list_t *list, int64_t item) {
    return bl_list_new(NULL, list, list->len+1, &item);
}

list_t *bl_list_insert(list_t *list, int64_t i, int64_t item) {
    if (i <= 1) return bl_list_prepend(list, item);
    else if (i >= list->len) return bl_list_append(list, item);
    else if (i <= list->before->len + 1) {
        return bl_list_new(
            bl_list_insert(list->before, i, item),
            list->after,
            list->len + 1, NULL);
    } else if (i > (list->len - list->after->len)) {
        return bl_list_new(
            list->before,
            bl_list_insert(list->after, i - (list->len - list->after->len), item),
            list->len + 1, NULL);
    } else {
        int64_t chunk1 = (i - list->before->len) - 1;
        int64_t chunk2 = list->len - list->after->len - chunk1;
        return bl_list_new(
            chunk1 <= 0 ? list->before : bl_list_new(
                list->before,
                bl_list_new(NULL, NULL, chunk1, list->items),
                list->before->len + chunk1,
                NULL),
            chunk2 <= 0 ? list->after : bl_list_new(
                bl_list_new(NULL, NULL, chunk2, &list->items[chunk1]),
                list->after,
                list->after->len + chunk2,
                NULL),
            list->len + 1,
            &item);
    }
}

list_t *bl_list_remove(list_t *list, int64_t i) {
    if (i < 1 || i > list->len) return list;
    else if (i <= list->before->len) {
        return bl_list_new(
            bl_list_remove(list->before, i),
            list->after,
            list->len - 1, NULL);
    } else if (i > (list->len - list->after->len)) {
        return bl_list_new(
            list->before,
            bl_list_remove(list->after, i - (list->len - list->after->len)),
            list->len - 1, NULL);
    } else {
        int64_t chunk1 = (i - list->before->len) - 1;
        int64_t chunk2 = (list->len - list->after->len - chunk1) - 1;
        return bl_list_new(
            chunk1 <= 0 ? list->before : bl_list_new(
                list->before,
                bl_list_new(NULL, NULL, chunk1, list->items),
                list->before->len + chunk1,
                NULL),
            chunk2 <= 0 ? list->after : bl_list_new(
                bl_list_new(NULL, NULL, chunk2, &list->items[chunk1 + 1]),
                list->after,
                list->after->len + chunk2,
                NULL),
            list->len - 1, NULL);
    }
}

list_t *bl_list_slice(list_t *list, int64_t first, int64_t next, int64_t last) {
    list_t *empty = bl_empty_list();
    int64_t step = next - first;
    int64_t len = list->len;
    if (step == 0 || (first < 1 && last < 1) || (first > len && last > len))
        return empty;

    first = MAX(1, MIN(len, first));
    last = MAX(1, MIN(len, last));
    if (first == 1 && last == len && step == 1) // Entire slice
        return list;

    int64_t slice_len = 0;
    for (int64_t i = first; step > 0 ? i <= last : i >= last; i += step)
        ++slice_len;

    if (slice_len == 0) return empty;

    if (step == 1) { // Optimization to avoid copying
        list_t *before = bl_list_slice(list->before, first, first+step, last);
        int64_t nonafter = list->len - list->after->len;
        list_t *after = bl_list_slice(list->after, first-nonafter, first-nonafter+step, last-nonafter);
        int64_t chunk_start = MAX(0, first - list->before->len - 1);
        int64_t chunk_len = slice_len - before->len - after->len;
        return bl_list_new(before, after, chunk_len, &list->items[chunk_start]);
    }

    size_t size = LIST_SIZE(slice_len);
    list_t *slice = calloc2(1, size);
    slice->len = slice_len;
    slice->before = empty;
    slice->after = empty;
    slice->depth = 1;
    int64_t dest = 0;
    for (int64_t i = first; step > 0 ? i <= last : i >= last; i += step)
        slice->items[dest++] = list->items[i-1];
    return (list_t*)intern_bytes_transfer((void*)slice, size);
}

list_t *bl_list_slice_range(list_t *list, range_t *r) {
    return bl_list_slice(list, r->first, r->next, r->last);
}
