#include <stdlib.h>
#include <err.h>

void *calloc3(int64_t nmem, int64_t size) {
    void *ret = calloc(nmem, size);
    if (!ret)
        err(1, "Memory allocation failure! (size = %lu x %lu)", nmem, size);
    return ret;
}

void *reallocarray3(void *ptr, int64_t nmem, int64_t size) {
    void *ret = reallocarray(ptr, nmem, size);
    if (!ret)
        err(1, "Memory allocation failure! (size = %lu x %lu)", nmem, size);
    return ret;
}
