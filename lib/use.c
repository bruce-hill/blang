#include <bhash.h>
#include <gc.h>
#include <dlfcn.h>
#include <err.h>
#include <libgen.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
#include <fcntl.h>

typedef void* (*bl_module_load)(void);

static hashmap_t *loaded = NULL;

void *bl_use(const char *from_file, const char *module_path) {
    if (!loaded) loaded = hashmap_new();
    const void *cached = hashmap_get(loaded, module_path);
    if (cached) return (void*)cached;

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
        if (!module) {
            if (asprintf(&path, "%s/%s/%s.bl", folder, module_dirname, module_basename) <= 0)
                errx(1, "Allocation failure");
            int test = open(path, O_RDONLY);
            if (test) {
                close(test);
                // Compile on-demand:
                char tmp[] = "/tmp/blang-module-XXXXXX.so";
                int xx = mkstemps(tmp, 3);
                if (!xx) errx(1, "Could not create temp file");
                close(xx);
                pid_t child = fork();
                if (!child) {
                    char *rpath = realpath(path, NULL);
                    chdir(cwd);
                    execvp("./blangc", (char*[]){"./blangc", "-c", rpath, "-s", tmp, NULL});
                }
                int status;
                waitpid(child, &status, 0);
                if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
                    free(path);
                    continue;
                }
                module = dlopen(tmp, RTLD_LAZY);
                free(path);
                if (module) goto load_module;
                else continue;
            } else {
                free(path);
            }
            continue;
        }
      load_module:;
        bl_module_load load_module = dlsym(module, "load");
        if (!load_module) continue;
        exports = load_module();
        if (exports) break;
    }
    free(copy);
    chdir(cwd);
    if (exports) hashmap_set(loaded, (void*)module_path, exports);
    return exports;
}
