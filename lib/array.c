#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>

#include "types.h"
#include "util.h"

array_t *bl_array_new(int64_t minsize) {
    array_t *array = calloc2(1, sizeof(array_t));
    if (minsize > 0)
        array->items = calloc2(minsize, sizeof(int64_t));
    return array;
}

void bl_array_free(array_t *array) {
    if (array->items) {
        free(array->items);
        array->items = NULL;
    }
    free(array);
}

void bl_array_append(array_t *array, int64_t item) {
    array->items = reallocarray2(array->items, array->len+1, sizeof(int64_t));
    array->items[array->len++] = item;
}

void bl_array_remove(array_t *array, int64_t i) {
    if (i < 1 || i > array->len) return;
    if (i < array->len)
        memmove(&array->items[i-1], &array->items[i], array->len - i);
    --array->len;
}

int64_t bl_array_nth(array_t *array, int64_t i) {
    if (i < 1 || i > array->len) return 0;
    return array->items[i-1];
}

void bl_array_set_nth(array_t *array, int64_t i, int64_t val) {
    if (i < 1 || i > array->len) return;
    array->items[i-1] = val;
}

array_t *bl_array_slice(array_t *array, range_t *r) {
    int64_t step = r->next - r->first;
    if (step == 0) return bl_array_new(0);

    int64_t first = r->first-1, last = r->last-1;
    int64_t len = array->len;
    int64_t slice_len;
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
    int64_t final_len = 0;
    for (int64_t i = first; step > 0 ? i <= last : i >= last; i += step)
        slice->items[final_len++] = array->items[i];
    slice->len = final_len;
    return slice;
}
