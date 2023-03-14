from apted import APTED, helpers

# src = "{A{B}{C}{D{E}{F}{G{H}{I}}{J{K}}}{L}}"
# tgt = "{D{F}{G{H}{I}}{J{K}}{L}}"

# tgt = "{subseteq{f{clos{A}}}{clos{f{A}}}}"
# src = "{subseteq{clos{B}}{C}}"

# src = "{f{C}}"
# tgt = "{clos{X}}"

# src = "{*{1}{inv{*{a}{b}}}}"
src = "{*{*{*{inv{b}}{inv{a}}}{*{a}{b}}}{inv{*{a}{b}}}}"
tgt = "{*{*{a}{b}}{inv{*{a}{b}}}}"
# tgt = "{*{inv{b}}{inv{a}}}"
# tgt = "{*{*{a}{b}}{inv{*{a}{b}}}}"

# src = "{*{a}{*{b}{c}}}"
# tgt = "{*{*{a}{b}}{c}}"

tree1 = helpers.Tree.from_text(src)
tree2 = helpers.Tree.from_text(tgt)

apted = APTED(tree1, tree2)
ted = apted.compute_edit_distance()
maps = apted.compute_edit_mapping()

print(f"distance: {ted}")

for edit_map in maps:
    print(' -> '.join(map(str, edit_map)))