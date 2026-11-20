module

public import Runcorn.GradientApproximation
public import Runcorn.HarmonicApproximation
public import Runcorn.FiniteModeTests
public import Runcorn.ApproximateTests

/-! # Passing from the separated moments to arbitrary harmonic pairs

Approximate each harmonic potential on a compact neighborhood of the shell by
finite sums of solid harmonics or their Kelvin transforms. A cutoff energy
identity gives convergence of each coordinate derivative in L² on the shell.
The two limits are taken in succession with the other gradient fixed.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set InnerProductSpace
namespace Runcorn

/-- The sufficiency step shared by Theorems 1 and 2. -/
theorem fixedTests_of_separated {n : ℕ} (hn : 2 ≤ n) {lo hi a b : ℝ}
    (hlo : 0 < lo) (ha : lo < a) (hab : a < b) (hb : b < hi) {f : Space n → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulus a b)))
    (hmom : ∀ (k : ℕ) (Y : Sphere n → ℂ), IsSphericalHarmonic k Y →
      ∀ m : ℤ, momentExponent n k m →
      (∫ x in annulus a b, f x * atDirection Y x * ((‖x‖ ^ m : ℝ) : ℂ)) = 0) :
    FixedTests lo hi a b f := by
  intro u v huv
  let K : Set (Space n) := annulus a b
  let I : Set (Space n) := {x | ‖x‖ < hi}
  let O : Set (Space n) := {x | lo < ‖x‖}
  have hK : IsCompact K := isCompact_annulus a b
  have hKI : K ⊆ I := fun x hx => lt_of_le_of_lt hx.2 hb
  have hKO : K ⊆ O := fun x hx => lt_of_lt_of_le ha hx.1
  have hinc : O ⊆ {x | x ≠ 0} := fun x hx => norm_pos_iff.mp (hlo.trans hx)
  have hiU (g) (hg : g ∈ interiorModeSpan n) := (interiorModeSpan_harmonic hg).mono (subset_univ I)
  have heV (g) (hg : g ∈ exteriorModeSpan n) := (exteriorModeSpan_harmonic hg).mono hinc
  obtain ⟨U,hU,hul⟩ := exists_gradient_approximants hK
    (isOpen_lt continuous_norm continuous_const) hKI huv.1
    (interiorModeSpan n : Set (Space n → ℂ)) hiU
    (fun C hC hsub _ hε => approximate_interior_on_compact (by omega : 0 < n) (((hlo.trans ha).trans hab).trans hb) huv.1 C hC hsub hε)
  obtain ⟨V,hV,hvl⟩ := exists_gradient_approximants hK
    (isOpen_lt continuous_const continuous_norm) hKO huv.2.1
    (exteriorModeSpan n : Set (Space n → ℂ)) heV
    (fun C hC hsub _ hε => approximate_exterior_on_compact hn hlo huv.2.1 huv.2.2 C hC hsub hε)
  have coord {g : Space n → ℂ} (hg : HarmonicOnNhd g K) (i : Fin n) :
      ContinuousOn (coordDerivative g i) K := fun x hx =>
    (((hg x hx).1.continuousAt_fderiv (by decide)).clm_apply continuousAt_const).continuousWithinAt
  apply annular_test_zero_of_gradient_approximations hf U V
    (fun j => coord ((hiU _ (hU j)).mono hKI)) (fun j => coord ((heV _ (hV j)).mono hKO))
    (coord (huv.1.mono hKI)) (coord (huv.2.1.mono hKO)) hul hvl
  exact fun N M => finite_mode_tests_zero hn (hlo.trans ha) hf hmom (hU N) (hV M)

end Runcorn
