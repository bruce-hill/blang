// Purely functional lists
#include <bhash.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>

#include "types.h"
#include "util.h"

static list_t *empty = NULL;

#define LIST_SIZE(n) (sizeof(list_t)+((n)-1)*sizeof(int64_t))

list_t *bl_empty_list(void) {
    if (empty == NULL) {
        size_t size = LIST_SIZE(0);
        empty = calloc2(1, size);
        empty->before = empty;
        empty->after = empty;
        empty = (list_t*)intern_bytes_transfer((char*)empty, size);
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

static list_t *coalesce(list_t *list) {
    size_t size = LIST_SIZE(list->len);
    list_t *compact = calloc2(1, size);
    compact->len = list->len;
    compact->before = bl_empty_list();
    compact->after = compact->before;
    compact->depth = 0;
    for (int64_t i = 1; i <= list->len; i++)
        compact->items[i-1] = bl_list_nth(list, i);
    compact = (list_t*)intern_bytes_transfer((char*)compact, size);
    return compact;
}

list_t *bl_list_new(list_t *before, list_t *after, int64_t len, int64_t *items) {
    if (len <= 0) return bl_empty_list();
    if (before == NULL) before = bl_empty_list();
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
        list = coalesce(list);
        if (tofree != list) free(tofree);
    } else {
        list = (list_t*)intern_bytes_transfer((char*)list, size);
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

list_t *bl_list_slice(list_t *list, range_t *r) {
    int64_t step = r->next - r->first;
    if (step == 0) return bl_empty_list();

    int64_t len = list->len;
    int64_t first = MAX(0, MIN(len-1, r->first-1)), last = MAX(0, MIN(len-1, r->last-1));
    int64_t slice_len = 0;
    for (int64_t i = first; step > 0 ? i <= last : i >= last; i += step)
        ++slice_len;

    size_t size = LIST_SIZE(slice_len);
    list_t *slice = calloc2(1, size);
    slice->len = slice_len;
    slice->before = bl_empty_list();
    slice->after = slice->before;
    slice->depth = 0;
    int64_t dest = 0;
    for (int64_t i = first; step > 0 ? i <= last : i >= last; i += step)
        slice->items[dest++] = list->items[i];
    return slice;
}
