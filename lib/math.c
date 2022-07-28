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
