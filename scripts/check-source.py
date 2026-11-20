"""Check the two public comparator targets and the isolation of the reference."""
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
config = json.loads((root / "comparator.json").read_text())
names = {"Runcorn.varyingAnnuli", "Runcorn.fixedAnnulus"}
allowed = {"propext", "Classical.choice", "Quot.sound"}
if (config.get("challenge_module"), config.get("solution_module")) != ("Challenge", "Solution"):
    raise SystemExit("Expected the modules Challenge and Solution in comparator.json.")
if len(config["theorem_names"]) != 2 or set(config["theorem_names"]) != names:
    raise SystemExit("The comparator must check both of the two introduction theorems.")
if not set(config["permitted_axioms"]) <= allowed:
    raise SystemExit("The comparator permits axioms outside the requested allowlist.")

def imports(source):
    """Return imports from this repository's one-module-per-line Lean headers."""
    return re.findall(r"^(?:public |private )?import\s+([\w.]+)[ \t]*$", source, re.M)

for module in ("Challenge", "Solution"):
    source = (root / f"{module}.lean").read_text()
    for full_name in names:
        name = full_name.split(".")[1]
        if not re.search(rf"^theorem {name}\b", source, re.M):
            raise SystemExit(f"{full_name} has no theorem declaration in {module}.lean.")

challenge_imports = imports((root / "Challenge.lean").read_text())
if not challenge_imports or not all(name.startswith("Mathlib.") for name in challenge_imports):
    raise SystemExit("The independent Challenge must import only Mathlib.")
for path in sorted(root.rglob("*.lean")):
    if ".lake" in path.parts or ".git" in path.parts:
        continue
    source = path.read_text()
    if not source.startswith("module\n"):
        raise SystemExit(f"{path.relative_to(root)} does not start with a module header.")
    if len(source.splitlines()) > 10_000:
        raise SystemExit(f"{path.relative_to(root)} exceeds 10,000 lines.")
    if path != root / "Challenge.lean" and "Challenge" in imports(source):
        raise SystemExit(f"{path.relative_to(root)} imports the independent reference.")
print("Source layout, the two theorem names, and the comparator axiom allowlist passed.")
