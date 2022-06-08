#include <assert.h>
#include <ctype.h>
#include <gc.h>
#include <gc/cord.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/param.h>

typedef struct intern_entry_s {
    char *mem;
    size_t len;
    struct intern_entry_s *next;
} intern_entry_t;

static intern_entry_t *interned = NULL, *lastfree = NULL;
static size_t intern_capacity = 0, intern_count = 0;

// Cache most recently used strings to prevent GC churn
#define N_RECENTLY_USED 256
static const char **recently_used = NULL;
static int recently_used_i = 0;

static void intern_insert(char *mem, size_t len);

static size_t hash_mem(const char *mem, size_t len)
{
    if (__builtin_expect(len == 0, 0)) return 0;
    register unsigned char *p = (unsigned char *)mem;
    register size_t h = (size_t)(*p << 7) ^ len;
    register size_t i = len > 128 ? 128 : len;
    while (i--)
        h = (1000003*h) ^ *p++;
    if (h == 0) h = 1234567;
    return h;
}

static void rehash()
{
    // Calculate new size to be min(16, next_highest_power_of_2(2 * num_entries))
    size_t new_size = 0;
    for (size_t i = 0; i < intern_capacity; i++)
        if (interned[i].mem)
            new_size += 2;
    if (new_size < 16) new_size = 16;
    size_t pow2 = 1;
    while (pow2 < new_size) pow2 <<= 1;
    new_size = pow2;

    intern_entry_t *old = interned;
    size_t old_capacity = intern_capacity;
    interned = calloc(new_size,sizeof(intern_entry_t));
    intern_capacity = new_size;
    intern_count = 0;
    lastfree = &interned[new_size - 1];
    // Rehash:
    if (old) {
        for (size_t i = 0; i < old_capacity; i++) {
            if (old[i].mem)
                GC_unregister_disappearing_link((void**)&old[i].mem);
            if (old[i].mem && old[i].len)
                intern_insert(GC_REVEAL_POINTER(old[i].mem), old[i].len);
        }
        free(old);
    }
}

static char *lookup(const char *mem, size_t len)
{
    if (intern_capacity == 0 || !mem) return NULL;
    int i = (int)(hash_mem(mem, len) & (size_t)(intern_capacity-1));
    for (intern_entry_t *e = &interned[i]; e; e = e->next) {
        if (e->mem && e->len == len && memcmp(mem, GC_REVEAL_POINTER(e->mem), len) == 0)
            return GC_REVEAL_POINTER(e->mem);
    }
    return NULL;
}

static void intern_insert(char *mem, size_t len)
{
    if (!mem || len == 0) return;

    // Grow the storage if necessary
    if ((intern_count + 1) >= intern_capacity)
        rehash();

    int i = (int)(hash_mem(mem, len) & (size_t)(intern_capacity-1));
    intern_entry_t *collision = &interned[i];
    if (!collision->mem) { // No collision
        collision->mem = (char*)GC_HIDE_POINTER(mem);
        assert(!GC_general_register_disappearing_link((void**)&collision->mem, mem));
        collision->len = len;
        ++intern_count;
        return;
    }

    while (lastfree >= interned && lastfree->len)
        --lastfree;

    int i2 = (int)(hash_mem(GC_REVEAL_POINTER(collision->mem), collision->len) & (size_t)(intern_capacity-1));
    if (i2 == i) { // Collision with element in its main position
        lastfree->mem = (char*)GC_HIDE_POINTER(mem);
        assert(!GC_general_register_disappearing_link((void**)&lastfree->mem, mem));
        lastfree->len = len;
        lastfree->next = collision->next;
        collision->next = lastfree;
    } else {
        intern_entry_t *prev = &interned[i2];
        while (prev->next != collision)
            prev = prev->next;
        memcpy(lastfree, collision, sizeof(intern_entry_t));
        assert(!GC_move_disappearing_link((void**)&collision->mem, (void**)&lastfree->mem));
        prev->next = lastfree;
        collision->mem = (char*)GC_HIDE_POINTER(mem);
        assert(!GC_general_register_disappearing_link((void**)&collision->mem, mem));
        collision->len = len;
        collision->next = NULL;
    }
    ++intern_count;
}

const char *intern_str(const char *str)
{
    if (!str) return NULL;
    size_t len = strlen(str) + 1;
    const char *intern = lookup(str, len);
    if (!intern) {
        char *tmp = GC_MALLOC_ATOMIC(len);
        memcpy(tmp, str, len);
        intern_insert(tmp, len);
        intern = tmp;
    }
    if (!recently_used) recently_used = GC_MALLOC(sizeof(char*)*N_RECENTLY_USED);
    recently_used[recently_used_i] = intern;
    recently_used_i = (recently_used_i + 1) & (N_RECENTLY_USED-1);
    return intern;
}
