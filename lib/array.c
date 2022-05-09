#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>

#include "types.h"

list_t *blang_list_new(long minsize) {
    list_t *list = calloc(1, sizeof(list_t));
    if (minsize > 0)
        list->items.ints = calloc(minsize, sizeof(long));
    return list;
}

void blang_list_free(list_t *list) {
    if (list->items.ints) {
        free(list->items.ints);
        list->items.ints = NULL;
    }
    free(list);
}

void blang_list_appendl(list_t *list, long item) {
    list->items.ints = reallocarray(list->items.ints, list->len+1, sizeof(long));
    list->items.ints[list->len++] = item;
}

void blang_list_appendd(list_t *list, double item) {
    list->items.floats = reallocarray(list->items.floats, list->len+1, sizeof(double));
    list->items.floats[list->len++] = item;
}

void blang_list_remove(list_t *list, long i) {
    if (i < 1 || i > list->len) return;
    if (i < list->len)
        memmove(&list->items.ints[i-1], &list->items.ints[i], list->len - i);
    --list->len;
}

long blang_list_nthl(list_t *list, long i) {
    if (i < 1 || i > list->len) return 0;
    return list->items.ints[i-1];
}

double blang_list_nthd(list_t *list, long i) {
    if (i < 1 || i > list->len) return nan("Missing");
    return list->items.floats[i-1];
}

void blang_list_set_nthl(list_t *list, long i, long val) {
    if (i < 1 || i > list->len) return;
    list->items.ints[i-1] = val;
}

void blang_list_set_nthd(list_t *list, long i, double val) {
    if (i < 1 || i > list->len) return;
    list->items.floats[i-1] = val;
}

list_t *blang_list_slice(list_t *list, Range *r) {
    long step = r->next - r->first;
    if (step == 0) return blang_list_new(0);

    long first = r->first-1, last = r->last-1;
    long len = list->len;
    long slice_len;
    if (step > 0) {
        first = MAX(first, 0);
        last = MIN(last, len-1);
        slice_len = MAX(1 + (last - first), len - first);
    } else {
        last = MAX(last, 0);
        first = MIN(first, len-1);
        slice_len = MAX(1 + (first - last), len - last);
    }
    list_t *slice = blang_list_new(slice_len);
    long final_len = 0;
    for (long i = first; step > 0 ? i <= last : i >= last; i += step)
        slice->items.ints[final_len++] = list->items.ints[i];
    slice->len = final_len;
    return slice;
}
