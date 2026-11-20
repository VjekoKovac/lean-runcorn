"""Run selected upstream Palomar intake checks against this checkout.

Pass a local PalomarRegistry/PalomarSubmission checkout as the one argument.
This script does not submit or upload anything.
"""
import hashlib
import sys
from pathlib import Path

project = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(sys.argv[1]).resolve()))
from scripts import source_requirements, submission_contract

metadata = project / "formalization.yaml"
manifest = submission_contract.load_formalization_metadata(metadata)
provenance = submission_contract.normalized_provenance(manifest)
print("formalization.yaml sha256", hashlib.sha256(metadata.read_bytes()).hexdigest())
print("Metadata and source attribution passed.")
print("Result origin", provenance["result_origin"])
print("Repository role", provenance["repository_role"])
summary, issues = source_requirements.inspect_lean_sources(project)
for issue in issues:
    print(issue)
if issues:
    raise SystemExit(1)
print("Lean source files inspected", summary["files_checked"])
print("Source format passed.")
