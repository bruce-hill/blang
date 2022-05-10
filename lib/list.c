// Purely functional lists
#include <bhash.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>

#include "types.h"
#include "util.h"

static list_t *empty = NULL;

#define LIST_SIZE(n) (sizeof(list_t)+((n)-1)*sizeof(long))

list_t *blang_empty_list(void) {
    if (empty == NULL) {
        size_t size = LIST_SIZE(0);
        empty = calloc2(1, size);
        empty->before = empty;
        empty->after = empty;
        empty = (list_t*)intern_bytes_transfer((char*)empty, size);
    }
    return empty;
}

long blang_list_nth(list_t *list, long i) {
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
    compact->before = blang_empty_list();
    compact->after = compact->before;
    compact->depth = 0;
    for (long i = 1; i <= list->len; i++)
        compact->items[i-1] = blang_list_nth(list, i);
    compact = (list_t*)intern_bytes_transfer((char*)compact, size);
    return compact;
}

list_t *blang_list_new(list_t *before, list_t *after, long len, long *items) {
    if (len <= 0) return blang_empty_list();
    if (before == NULL) before = blang_empty_list();
    if (after == NULL) after = empty;
    long nitems = len - (before->len + after->len);
    size_t size = LIST_SIZE(nitems);
    list_t *list = calloc2(1, size);
    list->before = before;
    list->after = after;
    list->len = len;
    list->depth = 1 + MAX(before->depth, after->depth);

    memcpy(list->items, items, nitems*sizeof(long));
    if (1<<list->depth > 3*list->len) {
        list_t *tofree = list;
        list = coalesce(list);
        if (tofree != list) free(tofree);
    } else {
        list = (list_t*)intern_bytes_transfer((char*)list, size);
    }
    return list;
}

list_t *blang_list_append(list_t *list, long item) {
    return blang_list_new(list, NULL, list->len+1, &item);
}

list_t *blang_list_prepend(list_t *list, long item) {
    return blang_list_new(NULL, list, list->len+1, &item);
}

list_t *blang_list_insert(list_t *list, long i, long item) {
    if (i <= 1) return blang_list_prepend(list, item);
    else if (i >= list->len) return blang_list_append(list, item);
    else if (i <= list->before->len + 1) {
        return blang_list_new(
            blang_list_insert(list->before, i, item),
            list->after,
            list->len + 1, NULL);
    } else if (i > (list->len - list->after->len)) {
        return blang_list_new(
            list->before,
            blang_list_insert(list->after, i - (list->len - list->after->len), item),
            list->len + 1, NULL);
    } else {
        long chunk1 = (i - list->before->len) - 1;
        long chunk2 = list->len - list->after->len - chunk1;
        return blang_list_new(
            chunk1 <= 0 ? list->before : blang_list_new(
                list->before,
                blang_list_new(NULL, NULL, chunk1, list->items),
                list->before->len + chunk1,
                NULL),
            chunk2 <= 0 ? list->after : blang_list_new(
                blang_list_new(NULL, NULL, chunk2, &list->items[chunk1]),
                list->after,
                list->after->len + chunk2,
                NULL),
            list->len + 1,
            &item);
    }
}

list_t *blang_list_remove(list_t *list, long i) {
    if (i < 1 || i > list->len) return list;
    else if (i <= list->before->len) {
        return blang_list_new(
            blang_list_remove(list->before, i),
            list->after,
            list->len - 1, NULL);
    } else if (i > (list->len - list->after->len)) {
        return blang_list_new(
            list->before,
            blang_list_remove(list->after, i - (list->len - list->after->len)),
            list->len - 1, NULL);
    } else {
        long chunk1 = (i - list->before->len) - 1;
        long chunk2 = (list->len - list->after->len - chunk1) - 1;
        return blang_list_new(
            chunk1 <= 0 ? list->before : blang_list_new(
                list->before,
                blang_list_new(NULL, NULL, chunk1, list->items),
                list->before->len + chunk1,
                NULL),
            chunk2 <= 0 ? list->after : blang_list_new(
                blang_list_new(NULL, NULL, chunk2, &list->items[chunk1 + 1]),
                list->after,
                list->after->len + chunk2,
                NULL),
            list->len - 1, NULL);
    }
}

list_t *blang_list_slice(list_t *list, range_t *r) {
    long step = r->next - r->first;
    if (step == 0) return blang_empty_list();

    long first = r->first-1, last = r->last-1;
    long len = list->len;
    long slice_len = 0;
    if (step > 0) {
        first = MAX(first, 0);
        last = MIN(last, len-1);
    } else {
        last = MAX(last, 0);
        first = MIN(first, len-1);
    }
    for (long i = first; step > 0 ? i <= last : i >= last; i += step)
        ++slice_len;

    size_t size = LIST_SIZE(slice_len);
    list_t *slice = calloc2(1, size);
    slice->len = slice_len;
    slice->before = blang_empty_list();
    slice->after = slice->before;
    slice->depth = 0;
    long dest = 0;
    for (long i = first; step > 0 ? i <= last : i >= last; i += step)
        slice->items[dest++] = list->items[i];
    return slice;
}
