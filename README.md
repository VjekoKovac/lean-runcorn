# A converse to generalized Runcorn's theorem

Lean 4 proofs of **Theorem 1** and **Theorem 2** of Vjekoslav Kovač and Ivica Smolić, *A converse to generalized Runcorn's theorem*, arXiv:2607.18379v1 (20 July 2026). Both the paper and the formalization are attributed to **Vjekoslav Kovač and Ivica Smolić**. AI agents wrote and reviewed the code. [Original paper](https://arxiv.org/abs/2607.18379v1) · [Theorem statements and proofs in the paper](https://arxiv.org/html/2607.18379v1)

| Result | What Lean proves | Declaration |
| --- | --- | --- |
| Varying annuli | For continuous complex data, vanishing against all admissible gradient products on every subannulus is equivalent to vanishing on every interior sphere. The solutions are radial for n ≥ 3. In dimension two their angular frequencies belong to {−1, 0, 1}. | `Runcorn.varyingAnnuli` |
| Fixed annulus | For complex L² data, vanishing against all admissible gradient products is equivalent to a spherical-harmonic expansion converging in annular L². In each degree the radial coefficients satisfy precisely the stated finite list of Laurent moment constraints. | `Runcorn.fixedAnnulus` |

Both theorems use every interior harmonic function and every exterior harmonic function tending to zero at infinity. The gradients are paired bilinearly. Complex conjugation enters the angular and radial Hilbert space pairings. The fixed-annulus theorem allows any degree-wise orthogonal basis, including bases whose vectors have arbitrary nonzero norms. The auxiliary theorem `Runcorn.exists_angularBasis` constructs a basis with the paper's degree-by-degree dimensions. [Basis construction](Runcorn/BasisExistence.lean) · [Dimension formula](Runcorn/Dimension.lean)

## Open the project in Lean

1. Extract the ZIP into an empty folder named `lean-runcorn-converse`. The file `lean-toolchain` and the folders `Runcorn` and `.github` should be directly inside it.
2. Install VS Code and its **Lean 4** extension. Complete the Lean setup offered by the extension, then use **File → Open Folder** to open the folder containing `lean-toolchain`. [Lean installation guide](https://lean-lang.org/install/)
3. Open **Terminal → New Terminal** in VS Code. On the first build, run the following commands from that folder. Lake uses the committed manifest to select dependencies.

```sh
lake exe cache get
lake build
lake env lean verification/PrincipalAxioms.lean
```

The last command prints the dependencies of each actual proof. In this release both lines list `[propext, Classical.choice, Quot.sound]`. The recorded output is in [verification/principal-axioms.txt](verification/principal-axioms.txt).

4. Open [Challenge.lean](Challenge.lean) and scroll to `theorem varyingAnnuli` or `theorem fixedAnnulus`. Use **Go to Definition** (F12) on `AngularForm`, `momentExponent`, or `HasMomentExpansion` to see the mathematical definitions. The two `sorry` bodies in this file mark the reference statements for Comparator.
5. Open [Solution.lean](Solution.lean) to see the proofs. Click inside a proof and look at the Lean Infoview for the current goal. Follow `fixedTests_hasMomentExpansion` for the forward implication of Theorem 2 and `fixedTests_of_separated` for the reverse implication. The files for the implementation import their own definitions.

## Check exactly what was verified

[verification/](verification/) contains the commands and output. [docs/verification.md](docs/verification.md) explains how to reproduce them, the three-axiom policy, and the difference between a build, a comparator check, and Palomar registration. [docs/statement-review.md](docs/statement-review.md) compares the complete statements with the source. [docs/proof-review.md](docs/proof-review.md) follows the paper's proof and explains the changes in the Lean argument. [docs/reuse.md](docs/reuse.md) identifies the main library results reused.

## Publish on GitHub and prepare a Palomar submission

1. Open the extracted project folder in VS Code. In **Source Control**, choose **Initialize Repository**, stage the files, and commit them. For example, use the commit message `Formalize both theorems on Runcorn's converse`. The .gitignore excludes the large local Lake cache.
2. Choose **Publish to GitHub** and select **public**. A suitable repository name is `lean-runcorn-converse`. On GitHub's **Code** tab, check that `Challenge.lean`, `Solution.lean`, `formalization.yaml`, `lakefile.toml`, and `lean-toolchain` appear at the first level. Include [the workflow](.github/workflows/lean.yml) in that first commit at exactly `.github/workflows/lean.yml`. GitHub Actions queues **Lean build** on the first push and on every later push, including a change only to `formalization.yaml`. If the repository is already published, use **Commit & Push** or **Sync Changes** in VS Code. A commit made in the GitHub web editor is already on GitHub. Open **Actions → Lean build** and select the run for your commit. The job **Build and verify both theorems** runs `lake build`, the axiom audit, and Lean Comparator. The runner starts when GitHub assigns it.
3. Inspect the public description, authors, maintainer, and license in [formalization.yaml](formalization.yaml). The project uses Apache-2.0 for its code, following the example repository. Review the statements yourself before describing them as author-reviewed.
4. After pushing your chosen commit, run `git rev-parse HEAD` in VS Code. Copy the complete 40-character SHA. On the Palomar submission form, select the public `owner/repository`, that SHA, the repository root as the project, and `comparator.json`. Both theorems are selected in this one configuration. Palomar performs its own verification and review. [Submission form](https://submit.palomar-registry.org) · [Submission requirements](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)

The reference project inspired the separation of independently readable statements from the proof implementation. Its Palomar identifier belongs to that project. [lean-dfr](https://github.com/roos-j/lean-dfr) · [Example Palomar entry](https://palomar-registry.org/entry?id=PALOMAR-2026-10-21-000004&version=1)
