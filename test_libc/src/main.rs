#![allow(unused)]

use libc::{PROT_NONE, PROT_READ, PROT_WRITE, MAP_PRIVATE, MAP_ANONYMOUS, MAP_NORESERVE};

fn mmap_prot_read_write(len: usize) -> *mut u8 {
    unsafe {
        let res = libc::mmap(
            // address 0 means the OS selects an address for us
            0 as *mut libc::c_void,
            len,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
            // The fd argument is ignored [if MAP_ANONYMOUS is specified); however,
            // some implementations require fd to be -1
            -1,
            0);
        if res == libc::MAP_FAILED {
            panic!("mmap failed");
        }
        res as *mut u8
    }
}

fn mmap_prot_none(len: usize) -> *mut u8 {
    unsafe {
        let res = libc::mmap(
            // address 0 means the OS selects an address for us
            0 as *mut libc::c_void,
            len,
            PROT_NONE,
            MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
            // The fd argument is ignored [if MAP_ANONYMOUS is specified); however,
            // some implementations require fd to be -1
            -1,
            0);
        if res == libc::MAP_FAILED {
            panic!("mmap failed");
        }
        res as *mut u8
    }
}

fn mprotect_prot_read_write(addr: *mut u8, len: usize) {
    unsafe {
        let res = libc::mprotect(
            addr as *mut libc::c_void,
            len,
            PROT_READ | PROT_WRITE);
        if res != 0 {
            panic!("mprotect failed");
        }
    }
}

fn mprotect_prot_none(addr: *mut u8, len: usize) {
    unsafe {
        let res = libc::mprotect(
            addr as *mut libc::c_void,
            len,
            PROT_NONE);
        if res != 0 {
            panic!("mprotect failed");
        }
    }
}

fn main() {
    unsafe {
        let p = mmap_prot_read_write(4096);
        *p = 5;
        println!("{:}", *p);

        mprotect_prot_none(p, 4096);
        mprotect_prot_read_write(p, 4096);
        
        *p = 7;
        println!("{:}", *p);
    }
}
