
typedef struct { long first, next, last; } Range;

typedef struct {
    long len;
    union {
        long *ints;
        double *floats;
    } items;
} list_t;
