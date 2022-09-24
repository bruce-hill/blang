#include <math.h>
#include <stdint.h>

double sane_fmod(double x, double y) {
    double ret = fmod(x, y);
    return ret < 0 ? ret + y : ret;
}

int64_t sane_lmod(int64_t x, int64_t y) {
    int64_t ret = x % y;
    return ret < 0 ? ret + y : ret;
}

int64_t ipow(int64_t base, int64_t exp) {
    int64_t result = 1;
    while (exp != 0) {
        if ((exp & 1) == 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }
    return result;
}

double d_mid(double x, double lo, double hi) {
    if (hi < lo) {
        double tmp = lo;
        lo = hi;
        hi = tmp;
    }

    if (x < lo)
        return lo;
    else if (x > hi)
        return hi;
    else
        return x;
}

int64_t l_mid(int64_t x, int64_t lo, int64_t hi) {
    if (hi < lo) {
        int64_t tmp = lo;
        lo = hi;
        hi = tmp;
    }

    if (x < lo)
        return lo;
    else if (x > hi)
        return hi;
    else
        return x;
}
