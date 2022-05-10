#include <math.h>

double sane_fmod(double x, double y) {
    double ret = fmod(x, y);
    return ret < 0 ? ret + y : ret;
}

long sane_lmod(long x, long y) {
    long ret = x % y;
    return ret < 0 ? ret + y : ret;
}

long ipow(int base, int exp) {
    long result = 1;
    while (exp != 0) {
        if ((exp & 1) == 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }
    return result;
}
