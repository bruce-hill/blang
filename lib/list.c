#include <stdlib.h>
#include <string.h>
#include <sys/param.h>

#include "types.h"

list_t *blang_list_new(long minsize) {
    return calloc(1+minsize, sizeof(long));
}

list_t *blang_list_appendl(list_t *list, long item) {
    list = reallocarray(list, 1+list->len+1, sizeof(long));
    list->items.ints[1+(list->len++)] = item;
    return list;
}

list_t *blang_list_appendf(list_t *list, double item) {
    list = reallocarray(list, 1+list->len+1, sizeof(long));
    list->items.floats[1+(list->len++)] = item;
    return list;
}

list_t *blang_list_remove(list_t *list, long i) {
    if (i < 1 || i > list->len) return list;
    if (i < list->len)
        memmove(&list->items.ints[i-1], &list->items.ints[i], list->len - i);
    --list->len;
    return list;
}

long blang_list_nthl(list_t *list, long i) {
    return list->items.ints[i];
}

double blang_list_nthf(list_t *list, long i) {
    return list->items.floats[i];
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
    list_t *slice = calloc(1+slice_len, sizeof(long));
    long final_len = 0;
    for (long i = first; step > 0 ? i <= last : i >= last; i += step)
        slice[final_len++] = list[i];
    slice->len = final_len;
    return slice;
}
