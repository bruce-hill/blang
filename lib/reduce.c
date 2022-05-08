
long any(long *vals) {
    long len = vals[0];
    for (long i = 1; i <= len; i++)
        if (vals[i]) return 1;
    return 0;
}

long all(long *vals) {
    long len = vals[0];
    for (long i = 1; i <= len; i++)
        if (!vals[i]) return 0;
    return 1;
}

long sum_int(long *vals) {
    long len = vals[0];
    long sum = 0;
    for (long i = 1; i <= len; i++)
        sum += vals[i];
    return sum;
}

long product_int(long *vals) {
    long len = vals[0];
    long product = 0;
    for (long i = 1; i <= len; i++)
        product *= vals[i];
    return product;
}

double sum_float(double *vals) {
    long len = ((long*)vals)[0];
    double sum = 0;
    for (long i = 1; i <= len; i++)
        sum += vals[i];
    return sum;
}

double product_float(double *vals) {
    long len = ((long*)vals)[0];
    double product = 0;
    for (long i = 1; i <= len; i++)
        product *= vals[i];
    return product;
}
