
#include <stdint.h>
typedef struct {
    int64_t first, next, last;
} range_t;

typedef struct {
    int64_t len;
    int64_t *items;
} array_t;

typedef struct {
    int64_t len;
    union {
        char *byte;
        int16_t *i16;
        int32_t *i32;
        int64_t *i64;
        float *f32;
        double *d32;
    } items;
} list_t;
