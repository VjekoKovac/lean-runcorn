"""Compare every dependency checkout's Git HEAD against the Lake manifest."""
import json
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / "lake-manifest.json").read_text())
for package in manifest["packages"]:
    directory = root / manifest["packagesDir"] / package["name"]
    actual = subprocess.check_output(
        ["git", "-C", directory, "rev-parse", "HEAD"], text=True
    ).strip()
    if actual != package["rev"]:
        raise SystemExit(f"{package['name']}: expected {package['rev']}, got {actual}")
    tracked = subprocess.check_output(
        ["git", "-C", directory, "status", "--porcelain", "--untracked-files=no"], text=True
    )
    if tracked:
        raise SystemExit(f"{package['name']}: changed tracked files")
    print(f"{package['name']} {actual} OK")
