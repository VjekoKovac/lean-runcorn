module

public import Runcorn.ModeSpans
public import Runcorn.Decay

/-! # Limits of finite exterior harmonic expansions -/
@[expose] public section
noncomputable section
open Set Filter Topology
namespace Runcorn

/-- A positive-degree decay exponent forces a homogeneous Kelvin mode to tend to zero. -/
theorem kelvinMode_tendsto_zero {n k : ℕ} (h : 2 - (n : ℤ) - k < 0)
    (P : Polynomial.Poly n) (hP : P.IsHomogeneous k) :
    Tendsto (kelvinMode k P) (comap (fun x : Space n => ‖x‖) atTop) (𝓝 0) := by
  let B := ‖polynomialOnSphere P‖
  have hr : Tendsto (fun x : Space n => ‖x‖) (comap (fun x : Space n => ‖x‖) atTop) atTop := tendsto_comap
  have hlim : Tendsto (fun x : Space n => B * ‖x‖ ^ (2 - (n : ℤ) - k))
      (comap (fun x : Space n => ‖x‖) atTop) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := B)).mul ((tendsto_zpow_atTop_zero h).comp hr)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hr.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  let σ : Sphere n := ⟨‖x‖⁻¹ • x, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),
      inv_mul_cancel₀ hx.ne']⟩
  have hrep : ‖x‖ • σ.val = x := by
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hx.ne', one_smul]
  have hval : polynomialValue P x = (‖x‖ : ℂ)^k * polynomialValue P σ.val := by
    rw [← polynomialValue_smul_of_homogeneous P hP, hrep]
  have hbound : ‖polynomialValue P σ.val‖ ≤ B := (polynomialOnSphere P).norm_coe_le_norm σ
  simp only [kelvinMode, hval, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x), abs_of_nonneg (zpow_nonneg (norm_nonneg x) _)]
  rw [show 2-(n:ℤ)-k = (2-(n:ℤ)-2*k)+(k:ℤ) by omega, zpow_add₀ hx.ne', zpow_natCast]
  calc
    _ ≤ ‖x‖ ^ (2-(n:ℤ)-2*k) * (‖x‖^k * B) := by gcongr
    _ = _ := by ring

/-- A finite exterior expansion has a limit at infinity. In n ≥ 3 the limit
is zero; in n = 2 the degree-zero mode may contribute a constant. -/
theorem exteriorModeSpan_limit {n : ℕ} (hn : 2 ≤ n) {U : Space n → ℂ}
    (hU : U ∈ exteriorModeSpan n) :
    ∃ c : ℂ, (3 ≤ n → c = 0) ∧ Tendsto U (comap (fun x : Space n => ‖x‖) atTop) (𝓝 c) := by
  apply Submodule.span_induction (p := fun U _ => ∃ c : ℂ, (3 ≤ n → c = 0) ∧
    Tendsto U (comap (fun x : Space n => ‖x‖) atTop) (𝓝 c)) _ _ _ _ hU
  · rintro _ ⟨k,P,hP,hΔ,rfl⟩
    by_cases h : 2-(n:ℤ)-k < 0
    · exact ⟨0,fun _ => rfl, kelvinMode_tendsto_zero h P hP⟩
    have hn2 : n = 2 := by omega
    have hk0 : k = 0 := by omega
    subst n k
    have hconst := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr hP)
    refine ⟨P.coeff 0, by omega, ?_⟩
    apply tendsto_const_nhds.congr
    intro x
    simp only [kelvinMode]
    rw [hconst, polynomialValue_C]
    norm_num
  · exact ⟨0, fun _ => rfl, tendsto_const_nhds⟩
  · rintro U V _ _ ⟨a,ha,hu⟩ ⟨b,hb,hv⟩
    exact ⟨a+b,fun hn => by simp [ha hn, hb hn],hu.add hv⟩
  · rintro c U _ ⟨a,ha,hu⟩
    exact ⟨c*a,fun hn => by simp [ha hn], tendsto_const_nhds.mul hu⟩

end Runcorn
