module

public import Runcorn.SphereDensity
public import Runcorn.Restriction
public import Runcorn.Orthogonality
public import Runcorn.Kelvin
public import Runcorn.GradientDecomposition

/-! # Traces of finite sums of interior and exterior solid harmonics -/
@[expose] public section
noncomputable section
open Set Metric InnerProductSpace Topology Filter
namespace Runcorn

/-- Finite sums of scalar multiples of mode functions from homogeneous
harmonic polynomials. -/
def modeSpan (n : ℕ) (M : ℕ → Polynomial.Poly n → Space n → ℂ) : Submodule ℂ (Space n → ℂ) :=
  Submodule.span ℂ {u | ∃ k P, P.IsHomogeneous k ∧ Polynomial.lap P = 0 ∧ u = M k P}

abbrev interiorModeSpan (n : ℕ) := modeSpan n (fun _ P => polynomialValue P)
abbrev exteriorModeSpan (n : ℕ) := modeSpan n kelvinMode

/-- Harmonicity extends from each mode to their finite span. -/
theorem modeSpan_harmonic {n : ℕ} {M : ℕ → Polynomial.Poly n → Space n → ℂ}
    {D : Set (Space n)}
    (hM : ∀ k P, P.IsHomogeneous k → Polynomial.lap P = 0 → HarmonicOnNhd (M k P) D)
    {u : Space n → ℂ} (hu : u ∈ modeSpan n M) : HarmonicOnNhd u D := by
  apply Submodule.span_induction (p := fun u _ => HarmonicOnNhd u D) _ _ _ _ hu
  · rintro _ ⟨k,P,hP,hΔ,rfl⟩
    exact hM k P hP hΔ
  · exact harmonicOnNhd_const 0
  · exact fun _ _ _ _ h h' => h.add h'
  · intro c U _ h
    exact h.comp_CLM (c • ContinuousLinearMap.id ℝ ℂ)

theorem interiorModeSpan_harmonic {n : ℕ} {u : Space n → ℂ} (hu : u ∈ interiorModeSpan n) :
    HarmonicOnNhd u univ :=
  modeSpan_harmonic (fun _ P _ h => harmonic_polynomialValue P h) hu

theorem exteriorModeSpan_harmonic {n : ℕ} {u : Space n → ℂ} (hu : u ∈ exteriorModeSpan n) :
    HarmonicOnNhd u {x | x ≠ 0} :=
  modeSpan_harmonic (fun _ P hP h => kelvin_harmonicOn P hP h) hu

/-- Uniform boundary approximation by finite linear combinations of modes
whose traces rescale the spherical harmonics by nonzero scalars. -/
theorem approximate_mode_trace {n : ℕ} (hn : 0 < n)
    (M : ℕ → Polynomial.Poly n → Space n → ℂ) {r : ℝ}
    (hM : ∀ k (P : Polynomial.Poly n), P.IsHomogeneous k → Polynomial.lap P = 0 →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ σ : Sphere n, M k P (r • σ.val) = c * polynomialValue P σ.val)
    (F : C(Sphere n, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ modeSpan n M, ∀ σ : Sphere n, ‖F σ - u (r • σ.val)‖ < ε := by
  let W := Submodule.span ℂ {Y : C(Sphere n, ℂ) | ∃ k, IsSphericalHarmonic k Y}
  have hcl : F ∈ closure (W : Set C(Sphere n, ℂ)) := by
    change F ∈ W.topologicalClosure
    rw [show W.topologicalClosure = ⊤ from harmonicRestrictions_span_dense hn]
    trivial
  obtain ⟨G,hG,hd⟩ := Metric.mem_closure_iff.mp hcl ε hε
  have hrep : ∃ u ∈ modeSpan n M, ∀ σ : Sphere n, u (r • σ.val) = G σ := by
    apply Submodule.span_induction (p := fun Z _ =>
      ∃ u ∈ modeSpan n M, ∀ σ : Sphere n, u (r • σ.val) = Z σ) _ _ _ _ hG
    · rintro Z ⟨k,P,hP,hH,hZ⟩
      have hΔ := polynomial_lap_eq_zero_of_harmonic P hH
      obtain ⟨c,hc,hc'⟩ := hM k P hP hΔ
      refine ⟨c⁻¹ • M k P, (modeSpan n M).smul_mem _ (Submodule.subset_span ⟨k,P,hP,hΔ,rfl⟩), ?_⟩
      intro σ
      simp only [Pi.smul_apply, smul_eq_mul, hc', inv_mul_cancel_left₀ hc, hZ]
    · exact ⟨0, (modeSpan n M).zero_mem, fun _ => rfl⟩
    · rintro U V _ _ ⟨u,hu,he⟩ ⟨v,hv,he'⟩
      exact ⟨u+v, (modeSpan n M).add_mem hu hv, fun σ => by simp [he, he']⟩
    · rintro c U _ ⟨u,hu,he⟩
      exact ⟨c • u, (modeSpan n M).smul_mem c hu, fun σ => by simp [he]⟩
  obtain ⟨u,hu,he⟩ := hrep
  refine ⟨u,hu,fun σ => ?_⟩
  rw [he, ← dist_eq_norm]
  exact (ContinuousMap.dist_apply_le_dist σ).trans_lt hd

theorem approximate_interior_trace {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (F : C(Sphere n, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ interiorModeSpan n, ∀ σ : Sphere n, ‖F σ - u (r • σ.val)‖ < ε := by
  apply approximate_mode_trace hn _ _ F hε
  intro k P hP _
  exact ⟨(r : ℂ)^k, pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne'),
    fun σ => polynomialValue_smul_of_homogeneous P hP r σ.val⟩

theorem approximate_exterior_trace {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (F : C(Sphere n, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u ∈ exteriorModeSpan n, ∀ σ : Sphere n, ‖F σ - u (r • σ.val)‖ < ε := by
  apply approximate_mode_trace hn _ _ F hε
  intro k P hP _
  refine ⟨((r ^ (2-(n:ℤ)-2*k) : ℝ) : ℂ) * (r : ℂ)^k,
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (zpow_ne_zero _ hr.ne')) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')), ?_⟩
  intro σ
  simp only [kelvinMode, norm_polarPoint_of_sphere r hr σ, polynomialValue_smul_of_homogeneous P hP, mul_assoc]

end Runcorn
