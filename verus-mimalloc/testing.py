import sys

def u64_leading_zeros(i):
    if i == 0:
        return 64
    else: 
        return u64_leading_zeros(i // 2) - 1

size = 72
def smallest(size):
    bytes_per_word = 8
    wsize = (size + bytes_per_word - 1) // bytes_per_word;
    w = (wsize - 1) 
    lz = u64_leading_zeros(w);
    b = (64 - 1 - lz)
    shifted = w >> (b - 2) 
    bin_idx = ((b * 4) + (shifted & 0x03)) - 3
    return bin_idx

def size_of_bin(bin_idx):
    assert(9 <= bin_idx)
    group = (bin_idx - 9) // 4;
    inner = (bin_idx - 9) % 4;
    return 8 * (inner + 5) * 2**(group + 1)

def pfd_lower(bin_idx):
    if bin_idx == 1:
        return 0
    else:
        size_of_bin(bin_idx - 1) // 8 + 1

def pfd_upper(bin_idx):
    return size_of_bin(bin_idx) // 8

def brute():
    for size in range(72, 129):
        print(f"smallest_bin_fitting_size({size}) == {smallest(size)},")
        
    for size in range(72, 129):
        print(f"assert(smallest_bin_fitting_size({size}) == {smallest(size)}) by (compute)")


    for size in range(72, 129):
        print(f"assert(pfd_lower({size}) == {pfd_lower(size)}) by (compute);")

    for size in range(72, 129):
        print(f"assert(pfd_upper({size}) == {pfd_upper(size)}) by (compute);")

def valid_sbin_idx(sbin_idx):
    return 0 <= sbin_idx <= 31

def size_of_sbin(sbin_idx): 
    if 0 <= sbin_idx and sbin_idx <= 7:
        return sbin_idx
    elif sbin_idx == 8:
        return 10
    else:
        group = (sbin_idx - 8) / 4;
        inner = (sbin_idx - 8) % 4;

        return ((inner + 5) * 2**(group + 1)) 

def smallest_sbin_fitting_size(i):
    if i <= 8:
        return i
    else:
        w = i - 1
        lz = u64_leading_zeros(w)
        b = 64 - 1 - lz
        sbin_idx = ((b << 2) | ((w >> (b - 2)) & 0x03)) - 4
        return sbin_idx
def p(i):
    sbin_idx = smallest_sbin_fitting_size(i);
    return valid_sbin_idx(sbin_idx) and size_of_sbin(sbin_idx) >= i

def q(slice_count):
    sbin_idx = smallest_sbin_fitting_size(slice_count)
    print(f"sbin_idx({slice_count}) = {sbin_idx}")
    print(f"size_of_sbin(sbin_idx) = {size_of_sbin(sbin_idx)}")
q(8)
q(9)
q(10)

for i in range(11, 513):
    if not p(i):

        print(f"Failed with i = {i}, sbin_idx = smallest_sbin_fitting_size({i}) = {smallest_sbin_fitting_size(i)} and valid_sbin_idx(smallest_sbin_fitting_size({i})) = {valid_sbin_idx(smallest_sbin_fitting_size(i))}")
        sys.exit(2)
