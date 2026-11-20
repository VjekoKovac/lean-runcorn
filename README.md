# A converse to generalized Runcorn's theorem

Lean 4 proofs of **Theorem 1** and **Theorem 2** of Vjekoslav Kovač and Ivica Smolić, *A converse to generalized Runcorn's theorem*, arXiv:2607.18379v1 (20 July 2026). Both the paper and the formalization are attributed to **Vjekoslav Kovač and Ivica Smolić**. AI agents wrote and reviewed the code. [Original paper](https://arxiv.org/abs/2607.18379v1) · [Theorem statements and proofs in the paper](https://arxiv.org/html/2607.18379v1)

| Result | What Lean proves | Declaration |
| --- | --- | --- |
| Varying annuli | For continuous complex data, vanishing against all admissible gradient products on every subannulus is equivalent to vanishing on every interior sphere. The solutions are radial for n ≥ 3. In dimension two their angular frequencies belong to {−1, 0, 1}. | `Runcorn.varyingAnnuli` |
| Fixed annulus | For complex L² data, vanishing against all admissible gradient products is equivalent to a spherical-harmonic expansion converging in annular L². In each degree the radial coefficients satisfy precisely the stated finite list of Laurent moment constraints. | `Runcorn.fixedAnnulus` |

Both theorems use every interior harmonic function and every exterior harmonic function tending to zero at infinity. The gradients are paired bilinearly. Complex conjugation enters the angular and radial Hilbert space pairings. The fixed-annulus theorem allows any degree-wise orthogonal basis, including bases whose vectors have arbitrary nonzero norms. The auxiliary theorem `Runcorn.exists_angularBasis` constructs a basis with the paper's degree-by-degree dimensions. [Basis construction](Runcorn/BasisExistence.lean) · [Dimension formula](Runcorn/Dimension.lean)

## Check exactly what was verified

[verification/](verification/) contains the commands and output. [docs/verification.md](docs/verification.md) explains how to reproduce them, the three-axiom policy, and the difference between a build, a comparator check, and Palomar registration. [docs/statement-review.md](docs/statement-review.md) compares the complete statements with the source. [docs/proof-review.md](docs/proof-review.md) follows the paper's proof and explains the changes in the Lean argument. [docs/reuse.md](docs/reuse.md) identifies the main library results reused.




