def get_alloc(allocator):
    res = []
    with open(allocator + "-out.txt") as f:
        go = False
        command_exited = False
        ncores = None
        for line in f:
            if line.startswith("benchmarking on "):
                t = line.split()
                assert ncores == None
                ncores = t[2]
                assert t[3] == "cores."
            elif line.startswith("# test "):
                assert not go
                go = True
            elif go:
                if line.startswith("Command exited") or line.startswith("Command terminated"):
                    assert not command_exited
                    command_exited = True
                else:
                    t = line.split()
                    if len(t) > 0:
                        bench = t[0]
                        assert t[1] == allocator
                        time = t[2]
                        assert len(t) == 8 or len(t) == 6 or len(t) == 7

                        if command_exited:
                            command_exited = False
                            res.append((bench, "fail"))
                        else:
                            res.append((bench, time))
                        
        assert go
        assert not command_exited

        print("cores for " + allocator + ": " + str(ncores))

        return res

def print_table(t):
    for (a, b, c) in t:
        a1 = " " * (16 - len(a))
        b1 = " " * (8 - len(b))
        print(a + a1 + b + b1 + c)

def print_latex_table(t):
    print("\\begin{tabular}{|l|r|r|}")
    print("\\hline")
    print("Benchmark & mimalloc & Verus mimalloc \\\\ \\hline")
    for (a, b, c) in t:
        a1 = " " * (16 - len(a))
        b1 = " " * (8 - len(b))
        print(a + a1 + "& " + b + " s." + b1 + "& " + c + " s.       \\\\ \\hline")
    print("\\end{tabular}")


vmi = get_alloc("vmi")
mi = get_alloc("mi")

table = [("bench", "mi", "vmi")]
for (a, b) in zip(mi, vmi):
    assert a[0] == b[0]
    table.append((a[0], a[1], b[1]))
print_table(table)

def float_to_string(f):
    f = float(f)
    if f < 1.0:
        return "%.2f" % f
    else:
        return "%.1f\\invizero" % f

latex_table = []
for (a, b) in zip(mi, vmi):
    assert a[0] == b[0]
    if b[1] != 'fail':
        assert a[1] != 'fail'
        x = float_to_string(a[1])
        y = float_to_string(b[1])
        latex_table.append((a[0], x, y))

print("")
print_latex_table(latex_table)
