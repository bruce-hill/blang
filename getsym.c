// Helper tool for getting dynamic library symbols
#include <err.h>
#include <dlfcn.h>
#include <fcntl.h>
#include <stdio.h>
#include <unistd.h>

int main(int argc, char *argv[]) {
    if (argc != 3) errx(1, "Usage: getsym filename symbol");
    int old_stdout = dup(STDOUT_FILENO);
    int dev_null = open("/dev/null", O_RDWR);
    dup2(dev_null, STDOUT_FILENO);
    dup2(dev_null, STDERR_FILENO);
    dup2(dev_null, STDIN_FILENO);
    void *dl = dlopen(argv[1], RTLD_LAZY);
    if (!dl) errx(1, "Failed to open dl file %s", argv[1]);
    void *sym = dlsym(dl, argv[2]);
    if (!sym) errx(1, "No such symbol %s", argv[2]);
    dprintf(old_stdout, "%s\n", (char*)sym);
    dlclose(dl);
    return 0;
}
