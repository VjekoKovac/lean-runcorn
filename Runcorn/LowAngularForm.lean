module

public import Runcorn.AngularLowSpace
public import Runcorn.Expansion

/-! # From slice-wise low spherical modes to continuous radial amplitudes -/
@[expose] public section
noncomputable section
open Set Topology
namespace Runcorn

/-- A slice in the span of the degree-zero harmonics is constant. -/
theorem lowAngularSpan_one_constant {n : ℕ} {F : C(Sphere n, ℂ)}
    (hF : F ∈ lowAngularSpan n 1) : ∃ c : ℂ, ∀ σ, F σ = c := by
  apply Submodule.span_induction (p := fun Z _ => ∃ c : ℂ, ∀ σ, Z σ = c) _ _ _ _ hF
  · intro Z hZ
    obtain ⟨k,hk,hY⟩ := hZ
    have hk' : k = 0 := by omega
    subst k
    exact degree_zero_is_constant hY
  · exact ⟨0, fun _ => rfl⟩
  · rintro U V _ _ ⟨a,ha⟩ ⟨b,hb⟩
    exact ⟨a+b, fun σ => by simp [ha, hb]⟩
  · rintro c U _ ⟨a,ha⟩
    exact ⟨c*a, fun σ => by simp [ha]⟩

/-- Interpolation of a trigonometric polynomial of degree at most one at
angles 0, π and π/2. The interpolation coefficients are independent of F. -/
theorem lowAngularSpan_two_circle {F : C(Sphere 2, ℂ)} (hF : F ∈ lowAngularSpan 2 2) (φ : ℝ) :
    F (circleDirection φ) =
      F (circleDirection 0) * ((1 + (Real.cos φ : ℂ) - (Real.sin φ : ℂ)) / 2) +
      F (circleDirection Real.pi) * ((1 - (Real.cos φ : ℂ) - (Real.sin φ : ℂ)) / 2) +
      F (circleDirection (Real.pi/2)) * (Real.sin φ : ℂ) := by
  let t : C(Sphere 2, ℂ) → Prop := fun F => F (circleDirection φ) =
    F (circleDirection 0) * ((1 + (Real.cos φ : ℂ) - (Real.sin φ : ℂ)) / 2) +
    F (circleDirection Real.pi) * ((1 - (Real.cos φ : ℂ) - (Real.sin φ : ℂ)) / 2) +
    F (circleDirection (Real.pi/2)) * (Real.sin φ : ℂ)
  change t F
  apply Submodule.span_induction (p := fun Z _ => t Z) _ _ _ _ hF
  · intro Z hZ
    obtain ⟨k,hk,hY⟩ := hZ
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · obtain ⟨c,hc⟩ := degree_zero_is_constant hY
      simp only [t, hc]
      ring
    · obtain ⟨c,hc⟩ := degree_one_is_linear hY
      simp [t, hc, circleDirection, polarPoint, Fin.sum_univ_two]
      ring
  · simp [t]
  · intro U V _ _ hU hV
    simp only [t, ContinuousMap.add_apply] at *
    rw [hU, hV]
    ring
  · intro c U _ hU
    simp only [t, ContinuousMap.smul_apply, smul_eq_mul] at *
    rw [hU]
    ring

/-- Constancy of every radial slice gives a scalar radial representative. -/
theorem radialOn_of_lowAngularSpan {n : ℕ} {lo hi : ℝ} (hlo : 0 < lo)
    {f : Space n → ℂ}
    (hs : ∀ r ∈ Ioo lo hi, ∃ F : C(Sphere n, ℂ), F ∈ lowAngularSpan n 1 ∧
      ∀ σ, F σ = f (r • σ.val)) :
    RadialOn lo hi f := by
  classical
  have hvals (r : ℝ) : ∃ c : ℂ, ∀ hr : r ∈ Ioo lo hi, ∀ σ : Sphere n, f (r • σ.val) = c := by
    by_cases hr : r ∈ Ioo lo hi
    · obtain ⟨F,hF,hσ⟩ := hs r hr
      obtain ⟨c,hc⟩ := lowAngularSpan_one_constant hF
      exact ⟨c, fun _ σ => (hσ σ).symm.trans (hc σ)⟩
    · exact ⟨0, fun hr' => (hr hr').elim⟩
  choose c hc using hvals
  refine ⟨c, fun x hx => ?_⟩
  have hnorm : 0 < ‖x‖ := hlo.trans hx.1
  let σ : Sphere n := ⟨‖x‖⁻¹ • x, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm),
      inv_mul_cancel₀ hnorm.ne']⟩
  have he : ‖x‖ • σ.val = x := by
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
  simpa only [he] using hc ‖x‖ hx σ

/-- Even when low-span membership is obtained separately at every radius,
sampling three fixed rays yields continuous coefficients for the Fourier modes. -/
theorem threeModes_of_lowAngularSpan {lo hi : ℝ} (hlo : 0 < lo) {f : Space 2 → ℂ}
    (hf : ContinuousOn f (shell lo hi))
    (hs : ∀ r ∈ Ioo lo hi, ∃ F : C(Sphere 2, ℂ), F ∈ lowAngularSpan 2 2 ∧
      ∀ σ, F σ = f (r • σ.val)) :
    ThreeModes lo hi f := by
  let v : ℝ → ℝ → ℂ := fun φ r => f (r • (circleDirection φ).val)
  have hv (φ : ℝ) : ContinuousOn (v φ) (Ioo lo hi) := by
    apply hf.comp (continuous_id.smul continuous_const).continuousOn
    intro r hr
    change lo < ‖r • (circleDirection φ).val‖ ∧ ‖r • (circleDirection φ).val‖ < hi
    rwa [norm_polarPoint_of_sphere r (hlo.trans hr.1) (circleDirection φ)]
  let c := fun r => (v 0 r + v Real.pi r) / 2
  let a := fun r => (v 0 r - v Real.pi r) / 2
  let b := fun r => v (Real.pi/2) r - c r
  have hc : ContinuousOn c (Ioo lo hi) := ((hv 0).add (hv Real.pi)).div_const _
  apply threeModes_of_cos_sin (c := c) (A := a) (B := b) hc
    (((hv 0).sub (hv Real.pi)).div_const _) ((hv _).sub hc)
  intro r hr φ
  have he : r • (circleDirection φ).val = polarPoint 2 r φ := by
    ext i
    fin_cases i <;> simp [circleDirection, polarPoint]
  obtain ⟨F,hF,hσ⟩ := hs r hr
  have h := lowAngularSpan_two_circle hF φ
  simp only [hσ] at h
  rw [← he, h]
  dsimp [a,b,c,v]
  ring

end Runcorn
