module

public import Runcorn.ModeTests
public import Runcorn.ModeSpans

/-! # Finite sums of interior and exterior harmonic tests
The bilinear form is linear in both arguments on smooth test functions. Thus the
single-mode sufficiency result extends to finite sums, including constant modes.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set MvPolynomial InnerProductSpace
namespace Runcorn
variable {n : ℕ} {a b : ℝ}
local notation "E" => Space n

private def testPair (f u v : E → ℂ) (a b : ℝ) := ∫ x in annulus a b, f x * gradDot u v x

private theorem testPair_symm (f u v : E → ℂ) :
    testPair f u v a b = testPair f v u a b := by simp [testPair,gradDot,mul_comm]

private theorem testPair_integrable {f u v : E → ℂ} (hf : MemLp f 2 (volume.restrict (annulus a b)))
    (hu : ∀ x ∈ annulus a b, ContDiffAt ℝ 2 u x) (hv : ∀ x ∈ annulus a b, ContDiffAt ℝ 2 v x) :
    IntegrableOn (fun x => f x * gradDot u v x) (annulus a b) := by
  have hK := isCompact_annulus (n := n) a b
  have : IsFiniteMeasure (volume.restrict (annulus (n := n) a b)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hL : IntegrableOn f (annulus a b) := hf.integrable (by norm_num)
  apply hL.mul_continuousOn _ hK
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply tendsto_finsetSum
  intro i _
  exact (((hu x hx).continuousAt_fderiv (by decide)).clm_apply continuousAt_const).mul
    (((hv x hx).continuousAt_fderiv (by decide)).clm_apply continuousAt_const)

private theorem testPair_add {f u w v : E → ℂ} (hf : MemLp f 2 (volume.restrict (annulus a b)))
    (hu : ∀ x ∈ annulus a b, ContDiffAt ℝ 2 u x) (hw : ∀ x ∈ annulus a b, ContDiffAt ℝ 2 w x)
    (hv : ∀ x ∈ annulus a b, ContDiffAt ℝ 2 v x) :
    testPair f (u+w) v a b = testPair f u v a b + testPair f w v a b := by
  unfold testPair
  rw [← integral_add (testPair_integrable hf hu hv) (testPair_integrable hf hw hv)]
  apply setIntegral_congr_fun (isCompact_annulus a b).measurableSet
  intro x hx
  dsimp only [gradDot]
  rw [fderiv_add ((hu x hx).differentiableAt (by decide)) ((hw x hx).differentiableAt (by decide))]
  simp [add_mul,Finset.sum_add_distrib,mul_add]

private theorem testPair_const_smul (f u v : E → ℂ) (c : ℂ) :
    testPair f (c • u) v a b = c * testPair f u v a b := by
  unfold testPair
  rw [← integral_const_mul]
  congr 1
  funext x
  simp [gradDot, fderiv_const_smul_field, mul_assoc, ← Finset.mul_sum, mul_left_comm]

private theorem testPair_span {f v : E → ℂ} (S : Set (E → ℂ))
    (hf : MemLp f 2 (volume.restrict (annulus a b)))
    (hS : ∀ u ∈ Submodule.span ℂ S, ∀ x ∈ annulus a b, ContDiffAt ℝ 2 u x)
    (hv : ∀ x ∈ annulus a b, ContDiffAt ℝ 2 v x)
    (h : ∀ u ∈ S, testPair f u v a b = 0) :
    ∀ u ∈ Submodule.span ℂ S, testPair f u v a b = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu => exact h u hu
  | zero => simp [testPair,gradDot]
  | add u w hu hw h0 h1 => rw [testPair_add hf (hS u hu) (hS w hw) hv,h0,h1,add_zero]
  | smul c u _ h0 => rw [testPair_const_smul,h0,mul_zero]

private theorem zero_mode_constant {P : Polynomial.Poly n} (hp : P.IsHomogeneous 0) :
    ∃ c : ℂ, polynomialValue P = fun _ => c := by
  have he := totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous _).mpr hp)
  exact ⟨_, he ▸ polynomialValue_C _⟩

/-- Finite harmonic modes annihilate every input whose separated moments vanish.
The degree-zero interior mode and the planar degree-zero exterior mode have zero gradient. -/
theorem finite_mode_tests_zero {n : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (ha : 0 < a) {f : Space n → ℂ} (hf : MemLp f 2 (volume.restrict (annulus a b)))
    (hmom : ∀ (k : ℕ) (Y : Sphere n → ℂ), IsSphericalHarmonic k Y →
      ∀ m : ℤ, momentExponent n k m →
        (∫ x in annulus a b, f x * atDirection Y x * ((‖x‖^m : ℝ) : ℂ)) = 0)
    {u v : Space n → ℂ} (hu : u ∈ interiorModeSpan n) (hv : v ∈ exteriorModeSpan n) :
    (∫ x in annulus a b, f x * gradDot u v x) = 0 := by
  have hI (u) (hu : u ∈ interiorModeSpan n) (x) (_ : x ∈ annulus a b) :
      ContDiffAt ℝ 2 u x := (interiorModeSpan_harmonic hu x (mem_univ x)).1
  have hE (v) (hv : v ∈ exteriorModeSpan n) (x) (hx : x ∈ annulus a b) :
      ContDiffAt ℝ 2 v x := (exteriorModeSpan_harmonic hv x (norm_pos_iff.mp (ha.trans_le hx.1))).1
  change testPair f u v a b = 0
  refine testPair_span _ hf hI (hE v hv) ?_ u hu
  rintro _ ⟨p, P, hp, hP, rfl⟩
  rw [testPair_symm]
  refine testPair_span _ hf hE (hI _ (Submodule.subset_span ⟨p,P,hp,hP,rfl⟩)) ?_ v hv
  rintro _ ⟨q, Q, hq, hQ, rfl⟩
  rw [testPair_symm]
  by_cases hp0 : p = 0
  · subst p
    obtain ⟨c,hc⟩ := zero_mode_constant hp
    simp [testPair,gradDot,hc]
  by_cases hqpos : n = 2 → 1 ≤ q
  · exact homogeneous_test_zero_of_separated hn ha hf hmom p q (by omega) hqpos P Q hp hq hP hQ
  · push Not at hqpos
    obtain ⟨rfl,hq0⟩ := hqpos
    have : q = 0 := by omega
    subst q
    obtain ⟨c,hc⟩ := zero_mode_constant hq
    have he : kelvinMode (n := 2) 0 Q = fun _ => c := by
      funext x
      simp [kelvinMode,hc]
    simp [testPair,gradDot,he]

end Runcorn
