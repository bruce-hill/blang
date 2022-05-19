// Wrapper around the Boehm Garbage Collector
#include <bhash.h>

void gc_init(void);
void *gc_alloc(size_t size);
void *gc_alloc_atomic(size_t size);
void *gc_realloc(void *ptr, size_t size);
void gc_free(void *ptr);
hashmap_t *gc_hashmap_new(hashmap_t *fallback);
