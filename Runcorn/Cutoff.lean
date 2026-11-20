module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# A compact radial test for orthogonality

The derivative in the squared-radius variable is a nonnegative tent supported
in [1,4]. Multiplying by any nonnegative integer power of the radius preserves
strict positivity of the integral on the annulus [1,2].
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace Runcorn

theorem exists_orthogonality_cutoff :
    ∃ c : ℝ → ℝ, ContDiff ℝ 1 c ∧
      (∀ s : ℝ, 4 ≤ s → c s = 0) ∧
      (∀ s : ℝ, s ∉ Icc 1 4 → deriv c s = 0) ∧
      (∀ m : ℕ, (∫ r in Icc (1 : ℝ) 2, deriv c (r^2) * r^m) ≠ 0) := by
  let w : ℝ → ℝ := fun t ↦ max 0 (min (t-1) (4-t))
  have hw : Continuous w := continuous_const.max ((continuous_id.sub continuous_const).min
    (continuous_const.sub continuous_id))
  let c : ℝ → ℝ := fun s ↦ ∫ t in (4:ℝ)..s, w t
  have hc (s : ℝ) : HasDerivAt c (w s) s := intervalIntegral.integral_hasDerivAt_right
    (hw.intervalIntegrable _ _) hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt
  have hc' : deriv c = w := funext fun s ↦ (hc s).deriv
  refine ⟨c, contDiff_one_iff_deriv.mpr ⟨fun s ↦ (hc s).differentiableAt, hc' ▸ hw⟩, ?_, ?_, ?_⟩
  · intro s hs
    change (∫ t in (4:ℝ)..s, w t) = 0
    rw [← intervalIntegral.integral_zero (a := 4) (b := s) (E := ℝ)]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hs]
    intro t ht
    exact max_eq_left ((min_le_right _ _).trans (sub_nonpos.mpr ht.1))
  · intro s hs
    rw [hc']
    apply max_eq_left
    by_cases h : s < 1
    · exact (min_le_left _ _).trans (sub_nonpos.mpr h.le)
    · exact (min_le_right _ _).trans (sub_nonpos.mpr (le_of_lt (lt_of_not_ge fun ht ↦ hs ⟨le_of_not_gt h,ht⟩)))
  · intro m
    rw [hc', integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (1:ℝ) ≤ 2)]
    have hcont : Continuous (fun r : ℝ ↦ w (r^2) * r^m) :=
      (hw.comp (continuous_id.pow 2)).mul (continuous_id.pow m)
    apply ne_of_gt
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _) ?_ (by norm_num)
    intro r hr
    have h1 : 0 < r^2 - 1 := by nlinarith [mul_pos (sub_pos.mpr hr.1) (show 0 < r+1 by linarith [hr.1])]
    have h2 : 0 < 4 - r^2 := by nlinarith [hr.1, hr.2, mul_pos (sub_pos.mpr hr.2) (show 0 < 2+r by linarith [hr.1])]
    exact mul_pos ((lt_min h1 h2).trans_le (le_max_right _ _)) (pow_pos (by linarith [hr.1]) _)

end Runcorn
