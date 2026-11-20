module

public import Runcorn.Fixed
public import Runcorn.Varying
public import Runcorn.TestRegularity
public import Runcorn.HighMoments
public import Runcorn.AngularSufficiency
public import Runcorn.FixedForward
public import Runcorn.ExpansionTests
public import Runcorn.Sufficiency

/-! # The two theorems of Kovač and Smolić, arXiv:2607.18379v1

The reference file is independent of this proof development. -/
@[expose] public section

noncomputable section
open MeasureTheory Set
namespace Runcorn

/-- The equivalence of volume tests on all subannuli and surface tests on all spheres.
The potential-theoretic characterization of their common kernel is a separate claim. -/
theorem annular_iff_surface {n : ℕ} (hn : 2 ≤ n) {lo hi : ℝ} (hlo : 0 < lo)
    (_hlohi : lo < hi) (f : Space n → ℂ) (hf : ContinuousOn f (shell lo hi)) :
    AllAnnularTests lo hi f ↔ AllSurfaceTests lo hi f := by
  have polar {a b : ℝ} (ha : lo < a) (hab : a < b) (hb : b < hi)
      {u v : Space n → ℂ} (h : Admissible lo hi u v) :
      (∫ x in annulus a b, f x * gradDot u v x) =
        ∫ r in a..b, surfaceIntegral (fun x => f x * gradDot u v x) r := by
    rw [intervalIntegral.integral_of_le hab.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact integral_annulus_polar hn (hlo.trans ha) (integrableOn_test hf h ha hb)
  constructor
  · intro h r hr u v huv
    apply (intervalIntegral_zero_iff (continuousOn_surfaceIntegral hlo.le
      (continuousOn_test hf huv))).mp _ r hr
    intro a b ha hab hb
    rw [← polar ha hab hb huv]
    exact h a b ha hab hb u v huv
  · intro h a b ha hab hb u v huv
    rw [polar ha hab hb huv]
    exact (intervalIntegral_zero_iff (continuousOn_surfaceIntegral hlo.le
      (continuousOn_test hf huv))).mpr (fun r hr => h r hr u v huv) a b ha hab hb

/-- Theorem 1. On every subannulus the tests vanish exactly for the radial
functions in dimension at least three and the three angular modes in dimension two.
The intermediate characterization by surface integrals holds in every dimension. -/
theorem varyingAnnuli (n : ℕ) (hn : 2 ≤ n) (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo < hi)
    (f : Space n → ℂ) (hf : ContinuousOn f (shell lo hi)) :
    (AllAnnularTests lo hi f ↔ AllSurfaceTests lo hi f) ∧
    (AllAnnularTests lo hi f ↔ AngularForm lo hi f) := by
  refine ⟨annular_iff_surface hn hlo hlohi f hf, angularForm_of_allAnnularTests hn hlo hf, ?_⟩
  intro h a b ha hab hb
  exact fixedTests_of_separated hn hlo ha hab hb (continuousOn_shell_memLp hf ha hb)
    (separated_tests_of_angularForm hn hlo ha hb hf h)

/-- Theorem 2. For an arbitrary degree-wise orthogonal basis, the exact fixed-shell
kernel consists of L²-convergent expansions with the specified Laurent moments. -/
theorem fixedAnnulus (n : ℕ) (hn : 2 ≤ n) (lo hi a b : ℝ) (hlo : 0 < lo) (ha : lo < a)
    (hab : a < b) (hb : b < hi) (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (f : Space n → ℂ) (hf : MemLp f 2 (volume.restrict (annulus a b))) :
    FixedTests lo hi a b f ↔ HasMomentExpansion a b Y f := by
  refine ⟨fixedTests_hasMomentExpansion hn hlo ha Y hY hf, fun h => ?_⟩
  exact fixedTests_of_separated hn hlo ha hab hb hf
    (hasMomentExpansion_separatedTests hn (hlo.trans ha) hY hf h)

end Runcorn
