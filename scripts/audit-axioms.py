#!/usr/bin/env python3
"""Prepare explicit #print axioms commands or validate their output.

Run from a checked-out repository root after building the local Lean modules.
Only named, public theorems and lemmas in Runcorn/*.lean and Solution.lean are
enumerated here. Lean itself computes each transitive axiom dependency.
"""
import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([^\s:(\[\{]+)")
REPORT = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$")
CLEAN = re.compile(r"^'([^']+)' does not depend on any axioms$")


def inventory():
    sources = sorted((ROOT / "Runcorn").glob("*.lean")) + [ROOT / "Solution.lean"]
    modules = []
    names = []
    for source in sources:
        module = ".".join(source.relative_to(ROOT).with_suffix("").parts)
        modules.append(module)
        namespace = []
        for line in source.read_text().splitlines():
            if m := re.fullmatch(r"namespace (\S+)", line):
                namespace.append(m[1])
            elif namespace and line == "end " + namespace[-1]:
                namespace.pop()
            elif m := DECL.match(line):
                names.append(".".join([*namespace, m[1]]))
    if len(names) != len(set(names)):
        raise SystemExit("duplicate names in the source inventory")
    return modules, names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", metavar="OUTPUT", type=Path)
    args = parser.parse_args()
    modules, names = inventory()
    if args.check is None:
        source = "module\n\n" + "".join(f"public import {m}\n" for m in modules)
        source += "\n/-! Transitive axiom dependencies of public project theorem declarations. -/\n\n"
        source += "".join(f"#print axioms {n}\n" for n in names)
        (ROOT / "Axioms.lean").write_text(source)
        print(f"Wrote {len(names)} explicit #print axioms commands to Axioms.lean")
        return
    seen = set()
    for line in args.check.read_text().splitlines():
        m = REPORT.match(line)
        if m:
            name = m[1]
            axioms = {s.strip() for s in m[2].split(",") if s.strip()}
            if forbidden := axioms - ALLOWED:
                raise SystemExit(f"{name} uses forbidden axioms: {sorted(forbidden)}")
        elif m := CLEAN.match(line):
            name = m[1]
        else:
            continue
        if name in seen:
            raise SystemExit(f"duplicate axiom report for {name}")
        seen.add(name)
    if seen != set(names):
        raise SystemExit(f"report names differ: {sorted(seen ^ set(names))}")
    print(f"All {len(seen)} theorem reports use only permitted axioms.")


if __name__ == "__main__":
    main()
