# Mathematical sources and reused Lean proofs

The informal source is Vjekoslav Kovač and Ivica Smolić, *A converse to generalized Runcorn's theorem*, arXiv:2607.18379v1. The null-power tests, the sharp dimension-dependent gradient-product decomposition, and the resulting Laurent exponents come from that paper. Its Section 2 cites Stein and Weiss and Axler, Bourdon, and Ramey for classical harmonic-function theory. [Paper and bibliography](https://arxiv.org/html/2607.18379v1)

All external mathematical imports used by the project are from Mathlib or its pinned dependency closure. The build uses Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Existing declarations are reused by import. The reference DFR repository was used for organization only. [Pinned Mathlib source and licence](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679) · [roos-j/lean-dfr](https://github.com/roos-j/lean-dfr)

| Part of the formalization | Reused Mathlib results | Local applications |
| --- | --- | --- |
| Euclidean harmonicity | `InnerProductSpace.HarmonicOnNhd`, `laplacian_eq_iteratedFDeriv_orthonormalBasis` in the inner-product-space library. Stefan Kebekus authored the harmonic definitions and Laplacian API. | `Definitions`, `PolynomialCalculus`, `Kelvin` |
| Polar integration and the fixed-shell Jacobian | `Measure.toSphere`, `measurePreserving_homeomorphUnitSphereProd`, Fubini for the Bochner integral, and change of variables for measure-preserving maps. | `Fixed`, `PolarMeasure`, `ProductSeries` |
| Vanishing moments on subintervals | The fundamental theorem of calculus for a continuous Banach-space-valued integrand. | `Runcorn.intervalIntegral_zero_iff` in `Runcorn/Varying.lean`. |
| Null powers and solid harmonics | `MvPolynomial.pderiv`, the multinomial formula for a power of a linear combination, `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`, and the squarefree/radical API. | `Algebra`, `Symbol`, `Quadric`, `FischerPairing`, `NullSpan` |
| Euler's homogeneous identity | `MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`, from Junyan Xu's `Mathlib.RingTheory.MvPolynomial.EulerIdentity`. | `Algebra`, `GradientDecomposition`, `Kelvin`, `Orthogonality` |
| Uniform angular density and annular L² expansions | Complex Stone–Weierstrass for a point-separating star subalgebra, `HilbertBasis.mk`, `HilbertBasis.hasSum_repr`, and `tendsto_integral_of_dominated_convergence`. | `SphereDensity`, `SphericalCompleteness`, `Series`, `RadialSeries`, `ProductSeries` |
| Green identities and local control of gradients | `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` supplies integration by parts in a coordinate direction. Smooth cutoffs use the Mathlib partition-of-unity library. | `Orthogonality`, `InteriorEstimate`, `GradientApproximation` |

The quoted declaration names can be opened with **Go to Definition** in VS Code. Each Mathlib file records its authors. The proof reviews explain which classical analytical steps were constructed in this project. [Proof correspondence](proof-review.md)
