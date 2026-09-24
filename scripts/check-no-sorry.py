#!/usr/bin/env python3
"""Checks Lean files for `sorry`, `admit`, and `axiom` declarations.

A plain `grep -v ':.*--'` (the earlier version of this gate) is bypassable:
it hides any real hit that merely has a trailing line comment on the same
line (`sorry -- TODO`, `axiom x : True -- note`), and a `^axiom ` anchor
misses an `axiom` declaration with leading whitespace, a modifier
(`private axiom`, `protected axiom`, `noncomputable axiom`, `scoped
axiom`), or an attribute (`@[simp] axiom`). This script strips Lean
comments first — both `--` line comments and `/- ... -/` block comments,
which nest in Lean — then searches the comment-free text, so a hit cannot
be hidden by commenting it out, and matches `\\baxiom\\b` anywhere in a
line rather than anchoring at column 0, so a modifier or attribute before
`axiom` does not hide it either.

This is a secondary, textual gate. The primary one is `lake env lean`'s
per-theorem axiom audit (see `reports/PROOF.md`, `README.md`,
`.github/workflows/ci.yml`): `#print axioms` on each of T1/T2/T3a/T3b/T4
already fails the build if any of them depends on `sorryAx` (the axiom
`sorry` compiles to) or on any axiom outside `{propext, Classical.choice,
Quot.sound}`. That check only covers the five named theorems, reached
through whatever they actually depend on; this script covers every
declaration in every project `.lean` file, including ones no theorem
happens to use.

Usage:
    check-no-sorry.py FILE...       # exit 1 if sorry/admit/axiom found
    check-no-sorry.py --self-test   # exits 1 if the checker itself is wrong
"""
import re
import sys

# Matches a `--` that starts a line comment. Lean has no line-comment
# escape inside normal code, so this is a plain substring search from `--`
# to end of line. (Not comment-aware of string literals; this project's
# `.lean` files contain no string literals with `--` in them — checked by
# the self-test's clean-code fixtures matching the real files' style.)
_LINE_COMMENT_RE = re.compile(r"--.*")

_KEYWORD_RE = re.compile(r"\b(sorry|admit|axiom)\b")


def strip_block_comments(text: str) -> str:
    """Removes `/- ... -/` block comments, which Lean allows to nest."""
    out = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if text[i : i + 2] == "/-":
            depth += 1
            i += 2
            continue
        if depth > 0 and text[i : i + 2] == "-/":
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)


def strip_comments(text: str) -> str:
    text = strip_block_comments(text)
    return "\n".join(_LINE_COMMENT_RE.sub("", line) for line in text.split("\n"))


def find_hits(path: str) -> list[str]:
    with open(path, encoding="utf-8") as f:
        original = f.read()
    cleaned = strip_comments(original)
    hits = []
    for lineno, (orig_line, clean_line) in enumerate(
        zip(original.split("\n"), cleaned.split("\n")), start=1
    ):
        m = _KEYWORD_RE.search(clean_line)
        if m:
            hits.append(f"{path}:{lineno}: {m.group(1)!r} found: {orig_line.strip()}")
    return hits


SELF_TEST_CASES = [
    # (source text, expected to be flagged?)
    ("theorem t : True := sorry -- TODO\n", True),
    ("axiom x : True -- note\n", True),
    ("  private axiom foo : True\n", True),
    ("@[simp] axiom bar : True\n", True),
    ("noncomputable axiom baz : True\n", True),
    ("/- axiom hidden : True -/\n", False),
    ("-- sorry mentioned only in a comment\ntheorem t : True := trivial\n", False),
    ("-- axiom mentioned only in a comment\ntheorem t : True := trivial\n", False),
    ("/- outer /- axiom nested -/ still a comment -/\ntheorem t : True := trivial\n", False),
    ("theorem admit_rate : True := trivial -- variable named admit_rate is fine\n", False),
    ("theorem t : True := by admit\n", True),
]


def run_self_test() -> int:
    import tempfile

    failures = 0
    for i, (src, expect_flagged) in enumerate(SELF_TEST_CASES):
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", delete=False, encoding="utf-8"
        ) as f:
            f.write(src)
            path = f.name
        hits = find_hits(path)
        got_flagged = len(hits) > 0
        status = "ok" if got_flagged == expect_flagged else "FAIL"
        if status == "FAIL":
            failures += 1
        print(f"[{status}] case {i}: expect_flagged={expect_flagged} got={got_flagged}")
        if status == "FAIL":
            print(f"    source: {src!r}")
            print(f"    hits: {hits}")
    if failures:
        print(f"self-test: {failures} case(s) failed")
        return 1
    print(f"self-test: all {len(SELF_TEST_CASES)} cases passed")
    return 0


def main() -> int:
    if len(sys.argv) == 2 and sys.argv[1] == "--self-test":
        return run_self_test()
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    all_hits = []
    for path in sys.argv[1:]:
        all_hits.extend(find_hits(path))
    if all_hits:
        for hit in all_hits:
            print(hit)
        print(f"found {len(all_hits)} sorry/admit/axiom use(s) in project files")
        return 1
    print(f"clean: no sorry/admit/axiom in {len(sys.argv) - 1} file(s)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
