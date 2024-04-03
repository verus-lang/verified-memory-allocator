#include <cstdlib>
#include <cstdint>

extern "C" {
    void* verus_mi_thread_init_default_heap();
    void* verus_mi_heap_malloc(void*, size_t);
    void verus_mi_free(void*);
}

thread_local void* default_heap = verus_mi_thread_init_default_heap();

extern "C" {

uint64_t thread_id_helper() {
    return (uint64_t)(uintptr_t)&default_heap;
}

/*
void* malloc(size_t size) {
    return verus_mi_heap_malloc(default_heap, size);
}

void free(void* ptr) {
    return verus_mi_free(ptr);
}
*/

void* get_default_heap() { return default_heap; }


}
