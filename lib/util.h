#pragma once

#include <stdlib.h>
#include <err.h>

static inline void *calloc2(size_t nmem, size_t size) {
    void *ret = calloc(nmem, size);
    if (!ret)
        err(1, "Memory allocation failure!");
    return ret;
}
