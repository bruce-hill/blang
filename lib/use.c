#include <dlfcn.h>
#include <err.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef void* (*bl_module_load)(void);

void *bl_use(const char *module_name) {
    const char *paths = getenv("BLANG_MODULE_PATHS");
    if (!paths) paths = ".";
    char *copy = strdup(paths);
    void *exports = NULL;
    for (char *folder; (folder = strsep(&copy, ":")) != NULL; ) {
        char *path = NULL;
        if (asprintf(&path, "%s/lib%s.so", folder, module_name) <= 0)
            errx(1, "Allocation failure");
        void *module = dlopen(path, RTLD_LAZY);
        free(path);
        if (!module) continue;
        bl_module_load load_module = dlsym(module, "load");
        if (!load_module) continue;
        exports = load_module();
        if (exports) break;
    }
    free(copy);
    return exports;
}
