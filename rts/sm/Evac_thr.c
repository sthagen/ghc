#if defined(THREADED_RTS) && !defined(js_HOST_ARCH)
#define PARALLEL_GC
#include "Evac.c"
#endif
