#include <stdint.h>

int64_t any(int64_t *vals) {
    int64_t len = vals[0];
    for (int64_t i = 1; i <= len; i++)
        if (vals[i]) return 1;
    return 0;
}

int64_t all(int64_t *vals) {
    int64_t len = vals[0];
    for (int64_t i = 1; i <= len; i++)
        if (!vals[i]) return 0;
    return 1;
}

int64_t sum_int(int64_t *vals) {
    int64_t len = vals[0];
    int64_t sum = 0;
    for (int64_t i = 1; i <= len; i++)
        sum += vals[i];
    return sum;
}

int64_t product_int(int64_t *vals) {
    int64_t len = vals[0];
    int64_t product = 0;
    for (int64_t i = 1; i <= len; i++)
        product *= vals[i];
    return product;
}

double sum_float(double *vals) {
    int64_t len = ((int64_t*)vals)[0];
    double sum = 0;
    for (int64_t i = 1; i <= len; i++)
        sum += vals[i];
    return sum;
}

double product_float(double *vals) {
    int64_t len = ((int64_t*)vals)[0];
    double product = 0;
    for (int64_t i = 1; i <= len; i++)
        product *= vals[i];
    return product;
}
