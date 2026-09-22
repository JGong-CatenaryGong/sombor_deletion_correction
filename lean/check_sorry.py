#!/usr/bin/env python3
"""Comment-aware `sorry`/`admit` check for the Lean sources.

Naively grepping for the word `sorry` matches documentation that *mentions*
`sorry`, so the sources are stripped of comments (nested block comments and
line comments) before the search.  Exit code 1 if a real occurrence is found.
"""
import os
import re
import sys

SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), "StarTheorem")


def strip_comments(text: str) -> str:
    """Remove Lean comments (nested `/- -/` and `--`), keeping strings intact."""
    out = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if depth == 0 and two == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth > 0:
            depth -= 1
            i += 2
        elif depth > 0:
            i += 1
        elif text[i] == '"':
            out.append(text[i])
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    out.append(text[i])
                    i += 1
                if i < n:
                    out.append(text[i])
                    i += 1
            if i < n:
                out.append(text[i])
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def main() -> int:
    bad = []
    for fn in sorted(os.listdir(SRC)):
        if not fn.endswith(".lean"):
            continue
        code = strip_comments(open(os.path.join(SRC, fn), encoding="utf-8").read())
        for m in re.finditer(r"\b(sorry|admit)\b", code):
            line = code[:m.start()].count("\n") + 1
            bad.append(f"StarTheorem/{fn}:{line}: {m.group(1)}")
    if bad:
        print("\n".join(bad))
        print("FOUND SORRY -- not a complete proof")
        return 1
    print("no 'sorry'/'admit' in the formalisation (comments excluded)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
