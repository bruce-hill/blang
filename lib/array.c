#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>

#include "types.h"
#include "util.h"

array_t *bl_array_new(long minsize) {
    array_t *array = calloc2(1, sizeof(array_t));
    if (minsize > 0)
        array->items = calloc2(minsize, sizeof(long));
    return array;
}

void bl_array_free(array_t *array) {
    if (array->items) {
        free(array->items);
        array->items = NULL;
    }
    free(array);
}

void bl_array_append(array_t *array, long item) {
    array->items = reallocarray2(array->items, array->len+1, sizeof(long));
    array->items[array->len++] = item;
}

void bl_array_remove(array_t *array, long i) {
    if (i < 1 || i > array->len) return;
    if (i < array->len)
        memmove(&array->items[i-1], &array->items[i], array->len - i);
    --array->len;
}

long bl_array_nth(array_t *array, long i) {
    if (i < 1 || i > array->len) return 0;
    return array->items[i-1];
}

void bl_array_set_nth(array_t *array, long i, long val) {
    if (i < 1 || i > array->len) return;
    array->items[i-1] = val;
}

array_t *bl_array_slice(array_t *array, range_t *r) {
    long step = r->next - r->first;
    if (step == 0) return bl_array_new(0);

    long first = r->first-1, last = r->last-1;
    long len = array->len;
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
    array_t *slice = bl_array_new(slice_len);
    long final_len = 0;
    for (long i = first; step > 0 ? i <= last : i >= last; i += step)
        slice->items[final_len++] = array->items[i];
    slice->len = final_len;
    return slice;
}
