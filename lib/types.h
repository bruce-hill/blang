
typedef struct { long first, next, last; } range_t;

typedef struct {
    long len;
    long *items;
} array_t;

typedef struct list_s {
    long len, depth;
    struct list_s *before, *after;
    long items[1];
} list_t;
