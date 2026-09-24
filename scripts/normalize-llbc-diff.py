#!/usr/bin/env python3
"""Compares two Charon LLBC JSON files for semantic equality.

Ignores exactly two things, both confirmed (by running Charon twice on an
unmodified crate) to vary between runs without changing the extracted
program: the `translated.options.dest_file` field (records the output path
the caller chose) and the list order of the `short_names` / `item_names` /
`assoc_item_names` debug-naming tables (association lists Charon does not
emit in a stable order). Every other field — `fun_decls`, `type_decls`,
`global_decls`, `trait_decls`, `trait_impls`, `ordered_decls`, `files`, and
the rest of `options` — is compared exactly.

Used by scripts/check-extraction.sh; see the comment there for why a plain
byte diff is not the right check for this file.
"""
import json
import sys


def normalize(path: str) -> dict:
    with open(path, encoding="utf-8") as f:
        data = json.load(f)
    translated = data.get("translated", {})
    options = translated.get("options")
    if isinstance(options, dict):
        options.pop("dest_file", None)
    for key in ("short_names", "item_names", "assoc_item_names"):
        table = translated.get(key)
        if isinstance(table, list):
            translated[key] = sorted(table, key=lambda kv: json.dumps(kv, sort_keys=True))
    return data


def main() -> int:
    if len(sys.argv) != 3:
        print(f"usage: {sys.argv[0]} <committed.llbc> <fresh.llbc>", file=sys.stderr)
        return 2
    a = normalize(sys.argv[1])
    b = normalize(sys.argv[2])
    if a != b:
        print("LLBC differs after normalization (dest_file and name-table order ignored)", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
