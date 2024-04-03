use core::ffi::c_void;

#[no_mangle]
pub unsafe extern "C" fn malloc(size: usize) -> *mut c_void {
    jemalloc_sys::malloc(size)
}

#[no_mangle]
pub unsafe extern "C" fn calloc(number: usize, size: usize) -> *mut c_void {
    jemalloc_sys::calloc(number, size)
}

#[no_mangle]
pub unsafe extern "C" fn realloc(ptr: *mut c_void, size: usize) -> *mut c_void {
    jemalloc_sys::realloc(ptr, size)
}

#[no_mangle]
pub unsafe extern "C" fn free(ptr: *mut c_void) {
    jemalloc_sys::free(ptr)
}
