import sys
import json

j = sys.stdin.read()
j = json.loads(j)

print(j["files"])

BOTTOM_FILES = ["types.rs", "os_mem.rs", "thread.rs"]
TOP_FILES = ["init.rs", "alloc_fast.rs", "free.rs"]

for f in BOTTOM_FILES:
    assert f in j["files"]
for f in TOP_FILES:
    assert f in j["files"]

bottom_trusted = 0
top_trusted = 0
for f in j["files"]:
    if 'trusted' in j["files"][f]:
        assert (f in BOTTOM_FILES) != (f in TOP_FILES)
        if f in BOTTOM_FILES:
            bottom_trusted += j["files"][f]["trusted"]
        else:
            top_trusted += j["files"][f]["trusted"]

total_exec = j["total"]["exec"]
total_spec_proof = j["total"]["proof"] + j["total"]["spec"]

total_total = bottom_trusted + top_trusted + total_exec + total_spec_proof
    
print("\\newcommand{\\allocatorTopBread}{%d}" % top_trusted)
print("\\newcommand{\\allocatorBottomBread}{%d}" % bottom_trusted)
print("\\newcommand{\\allocatorTotalTrusted}{%d}" % (top_trusted + bottom_trusted))
print("\\newcommand{\\allocatorExec}{%d}" % total_exec)
print("\\newcommand{\\allocatorProof}{%d}" % total_spec_proof)
print("\\newcommand{\\allocatorProofToCodeRatio}{%.1f}" % (total_spec_proof / total_exec))
print("\\newcommand{\\allocatorTotal}{%d}" % total_total)

a = j["files"]["tokens.rs"]["proof"] + j["files"]["tokens.rs"]["spec"]
b = j["files"]["page_organization.rs"]["proof"] + j["files"]["page_organization.rs"]["spec"]
print("\\newcommand{\\allocatorMimProof}{%d}" % a)
print("\\newcommand{\\allocatorPageOrgProof}{%d}" % b)
print("\\newcommand{\\allocatorProofMinus}{%d}" % (total_spec_proof - a - b))
