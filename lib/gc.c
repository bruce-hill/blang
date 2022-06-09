// Wrapper around the Boehm Garbage Collector
#include <bhash.h>
#include <err.h>
#include <gc.h>

void gc_init(void) {
    GC_INIT();
    hashmap_set_allocator(GC_malloc, GC_free);
}

void *gc_alloc(size_t size) {
    void *ret = GC_MALLOC(size);
    if (!ret)
        err(1, "Memory allocation failure!");
    return ret;
}

void *gc_calloc(size_t size, size_t nmem) {
    return gc_alloc(size * nmem);
}

void *gc_alloc_atomic(size_t size) {
    void *ret = GC_MALLOC_ATOMIC(size);
    if (!ret)
        err(1, "Memory allocation failure!");
    return ret;
}

void *gc_realloc(void *ptr, size_t size) {
    void *ret = GC_REALLOC(ptr, size);
    if (!ret)
        err(1, "Memory allocation failure!");
    return ret;
}

void gc_free(void *ptr) {
    GC_FREE(ptr);
}
