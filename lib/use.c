#include <dlfcn.h>
#include <err.h>
#include <libgen.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

typedef void* (*bl_module_load)(void);

void *bl_use(const char *from_file, const char *module_path) {
    const char *paths = getenv("BLANG_MODULE_PATHS");
    if (!paths) paths = ".";
    char *copy = strdup(paths);
    void *exports = NULL;
    char cwd[PATH_MAX] = {0};
    getcwd(cwd, PATH_MAX);
    char buf[PATH_MAX] = {0};
    strncpy(buf, from_file, sizeof(buf));
    char *from_dir = dirname(buf);
    chdir(from_dir);
    char module_parts[PATH_MAX];
    strncpy(module_parts, module_path, sizeof(module_parts));
    char *module_basename = basename(module_parts);
    char *module_dirname = dirname(module_parts);

    for (char *folder; (folder = strsep(&copy, ":")) != NULL; ) {
        char *path = NULL;
        if (asprintf(&path, "%s/%s/lib%s.so", folder, module_dirname, module_basename) <= 0)
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
    chdir(cwd);
    return exports;
}
