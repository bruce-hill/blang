// Simple API for interning values.
// Interned values are garbage collected using the Boehm garbage collector (not
// immortal), but the most recently interned items are kept in memory to
// prevent churn.
#pragma once

const void *intern_bytes(const char *bytes, size_t len);
const char *intern_str(const char *str);
