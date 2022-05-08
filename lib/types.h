
typedef struct { long first, next, last; } Range;

typedef struct {
    long len;
    union {
        long ints[1];
        double floats[1];
    } items;
} list_t;
