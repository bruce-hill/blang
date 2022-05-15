
#include <stdint.h>
typedef struct { int64_t first, next, last; } range_t;

typedef struct {
    int64_t len;
    int64_t *items;
} array_t;

typedef struct {
    int64_t len;
    int64_t *items;
} list_t;
