# Reproducing the verification

## The two certified declarations

| Lean name | Mathematical scope | Axioms printed by Lean |
| --- | --- | --- |
| `Runcorn.varyingAnnuli` | Theorem 1, including both equivalences and both dimension cases | `propext`, `Classical.choice`, `Quot.sound` |
| `Runcorn.fixedAnnulus` | Theorem 2, both implications for every degree-wise orthogonal basis on the unit sphere | `propext`, `Classical.choice`, `Quot.sound` |

`propext` identifies logically equivalent propositions. `Classical.choice` allows a witness to be chosen from an existence proof. `Quot.sound` identifies quotient representatives related by the defining equivalence relation, as in spaces of functions modulo almost-everywhere equality. The full dependency audit uses the three-axiom allowlist in `comparator.json`. Both solution declarations are closed theorems with the hypotheses of the paper. [Printed axioms for the two proofs](../verification/principal-axioms.txt) · [Reference and solution digests](../verification/comparator-inputs.txt)

Lean also printed the transitive axioms for 205 named public theorems and lemmas, including the existence and dimension of the angular bases. The audit matched all 205 reports to the source inventory and accepted each axiom set. [All 205 axiom reports](../verification/all-axioms.txt)

The standalone `Challenge.lean` imports Mathlib. Its only two placeholders are the reference theorem bodies. `Solution.lean` imports the implementation's copies of the definitions and the proved modules under `Runcorn/`. The reference and solution are elaborated separately. Comparator compares the named declarations and their dependencies and checks the solution proof terms. Independent AI reviews compare the actual statements with the mathematical paper, and describe the proof route. [Statement review](statement-review.md) · [Proof review](proof-review.md)

## Commands

From the project root with the pinned Lean installation active, run the following.

```sh
lean --version
lake --version
lake exe cache get
lake build
lake env lean verification/PrincipalAxioms.lean
lake env lean Axioms.lean > runcorn-axioms.log
python3 scripts/audit-axioms.py --check runcorn-axioms.log
lake env lean verification/MomentCases.lean
python3 scripts/check-source.py
python3 scripts/check-revisions.py
```

The development used Lean 4.35.0, Lake 5.0.0-src+eb6cafb, and Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The original verification machine had the pinned external dependencies and Mathlib objects available locally. A fresh project build used this dependency cache. The commands above allow a new machine to fetch it. [Tool versions and dependency revisions](../verification/versions.txt) · [Build transcript](../verification/build.txt) · [Source-layout check](../verification/source-check.txt) · [Dependency check](../verification/dependency-check.txt)

The Laurent exponent checks use `omega`, simplification, and kernel reduction via `decide`. Polynomial identities use `ring` and `ring_nf`; inequalities and scalar simplifications also use `norm_num`, `linarith`, and `positivity`. These tactics produce Lean proof terms. For example the explicit case checks establish empty exponent sets for (2,0) and (2,1), the single exponent −2 for (2,2) and (3,1), and the exponents −3 and −1 for (3,2). The theorem proofs also justify the index ranges in arbitrary dimension. [Independent low-degree checks](../verification/MomentCases.lean) · [Actual output](../verification/moment-cases.txt)

## Replay the comparator

On Linux, with bubblewrap installed and user namespaces available, run these from the project root.

```sh
lake comparator --config comparator.json
bash scripts/replay-kernels.sh
```

The first command uses the local Lean comparator. The second uses the same two declarations and allowlist, makes a temporary configuration with the independent checker executables supplied by the pinned release, and asks for con-ron and NanoDa as well as the default kernel. The ordinary configuration in the root is suitable for the Palomar form. On the verification host, the exact invocation used a wrapper for its network-namespace restrictions. Its source and explanation are included with the log. [Full comparator transcript](../verification/comparator.txt) · [Replay script](../scripts/replay-kernels.sh) · [Host details](../verification/host/README.md)

## Palomar preparation

The local input check invokes PalomarSubmission's metadata, provenance, and Lean source-layout functions at commit `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. To reproduce it, pass a checkout of that revision to `python3 verification/check-palomar-input.py /path/to/PalomarSubmission`. [Intake check output](../verification/palomar-input.txt) · [Upstream checker](https://github.com/PalomarRegistry/PalomarSubmission/tree/14aa8d6b3c2f14a8540605e37144560b9a00e7e7)

The package includes GitHub Actions configuration. A GitHub-hosted workflow run, Palomar's own mechanical report, its editorial review, and a registration identifier require a published commit and the external services. This package records local certification and the AI reviews. The review and publication steps for the authors are in the [README](../README.md).
