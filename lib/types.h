
#include <stdint.h>
typedef struct { int64_t first, next, last; } range_t;

typedef struct {
    int64_t len;
    int64_t *items;
} array_t;

typedef struct list_s {
    int64_t len, depth;
    struct list_s *before, *after;
    int64_t items[1];
} list_t;
