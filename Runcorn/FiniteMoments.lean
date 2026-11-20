module

public import Runcorn.Orthogonality
public import Runcorn.PolarMeasure

/-! # Separated tests against finite degree expansions in Theorem 2

Angular orthogonality eliminates every degree except that of the spherical
test. Each remaining term is the product of a fixed angular scalar and one
of the vanishing radial moments prescribed by the paper.
-/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory

namespace Runcorn

theorem radialLaurent_memLp {n : ℕ} {a b : ℝ} (ha : 0 < a) (m : ℤ) :
    MemLp (fun r : ℝ ↦ ((r ^ m : ℝ) : ℂ)) 2 (radialMeasure n a b) := by
  let w := fun r : ℝ ↦ ((r ^ m : ℝ) : ℂ)
  have h : ContinuousOn w (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn (continuous_id.continuousOn.zpow₀ m
      fun _ hx ↦ Or.inl (ha.trans_le hx.1).ne')
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn h
  apply MemLp.of_bound (μ := radialMeasure n a b) (h.aestronglyMeasurable measurableSet_Icc |>.mono_ac
    (withDensity_absolutelyContinuous _ _)) C
  filter_upwards [ae_radial_mem n a b] with r hr using hC r hr

/-- The angular integral of a finite degree-truncation has just one possibly
nonzero degree, whether or not the target degree is included in the truncation. -/
theorem angularIntegral_partialExpansion {n k : ℕ} (hn : 2 ≤ n)
    (Y : AngularFamily n) (hY : IsAngularBasis Y) (g : Coefficients n)
    (N : ℕ) (Z : Sphere n → ℂ) (hZ : IsSphericalHarmonic k Z) {r : ℝ} (hr : 0 < r) :
    angularIntegral (partialExpansion Y g N) Z r =
      if k < N then ∑ j, g k j r * (∫ σ, Y k j σ * Z σ ∂surfaceMeasure n) else 0 := by
  classical
  let I := fun d (j : Fin (harmonicDimension n d)) ↦
    ∫ σ, Y d j σ * Z σ ∂surfaceMeasure n
  let term := fun d (j : Fin (harmonicDimension n d)) (σ : Sphere n) ↦
    g d j r * (Y d j σ * Z σ)
  have hint (d) (j : Fin (harmonicDimension n d)) : Integrable (term d j) (surfaceMeasure n) := by
    have hc : Continuous (term d j) := continuous_const.mul (((hY d).1 j).continuous.mul hZ.continuous)
    unfold surfaceMeasure
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hzero (d : ℕ) (hd : d ≠ k) (j : Fin (harmonicDimension n d)) : I d j = 0 :=
    integral_mul_eq_zero_of_degree_ne hn hd ((hY d).1 j) hZ
  calc
    _ = ∫ σ, ∑ d ∈ Finset.range N, ∑ j, term d j σ ∂surfaceMeasure n := by
      apply integral_congr_ae
      filter_upwards with σ
      simp only [partialExpansion_polar _ _ _ _ hr, Finset.sum_mul, mul_assoc, term]
    _ = ∑ d ∈ Finset.range N, ∑ j, g d j r * I d j := by
      rw [integral_finsetSum _ (fun d _ ↦ integrable_finsetSum _ (fun j _ ↦ hint d j))]
      apply Finset.sum_congr rfl
      intro d hd
      rw [integral_finsetSum _ (fun j _ ↦ hint d j)]
      simp only [term, integral_const_mul, I]
    _ = _ := by
      by_cases h : k < N
      · rw [ite_eq_left h]
        exact Finset.sum_eq_single k (fun d _ hd ↦ by simp [hzero d hd])
          (fun hk ↦ False.elim (hk (Finset.mem_range.mpr h)))
      · rw [ite_eq_right h]
        apply Finset.sum_eq_zero
        intro d hd
        have hdk : d ≠ k := by have := Finset.mem_range.mp hd; omega
        simp [hzero d hdk]

theorem finiteExpansion_test_zero {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} (ha : 0 < a)
    (Y : AngularFamily n) (hY : IsAngularBasis Y) (g : Coefficients n)
    (hg : ∀ k j, InMomentSpace n k a b (g k j)) (N : ℕ)
    (hN : MemLp (partialExpansion Y g N) 2 (volume.restrict (annulus a b)))
    {k : ℕ} (Z : Sphere n → ℂ) (hZ : IsSphericalHarmonic k Z)
    {m : ℤ} (hm : momentExponent n k m) :
    (∫ x in annulus a b, partialExpansion Y g N x * atDirection Z x * ((‖x‖ ^ m : ℝ) : ℂ)) = 0 := by
  rw [annular_pairing_eq_radial_moment hn ha _ _ _ (integrableOn_separatedTest ha hN hZ.continuous m)]
  let ν := radialMeasure n a b
  let c := fun j : Fin (harmonicDimension n k) ↦ ∫ σ, Y k j σ * Z σ ∂surfaceMeasure n
  let w := fun r : ℝ ↦ ((r ^ m : ℝ) : ℂ)
  have h (r : ℝ) (hr : r ∈ Icc a b) :=
    angularIntegral_partialExpansion hn Y hY g N Z hZ (ha.trans_le hr.1)
  by_cases hk : k < N
  · have hent (j : Fin (harmonicDimension n k)) : Integrable (fun r ↦ (g k j r * w r) * c j) ν :=
      ((hg k j).1.integrable_mul (radialLaurent_memLp ha m)).mul_const _
    calc
      _ = ∫ r, ∑ j, (g k j r * w r) * c j ∂ν := by
        apply integral_congr_ae
        filter_upwards [ae_radial_mem n a b] with r hr
        simp only [h r hr, ite_eq_left hk, Finset.sum_mul, c, w, mul_right_comm (g _ _ r)]
      _ = _ := by
        rw [integral_finsetSum _ (fun j _ ↦ hent j)]
        apply Finset.sum_eq_zero
        intro j hj
        rw [integral_mul_const, (hg k j).2 m hm, zero_mul]
  · have hzero : (fun r ↦ angularIntegral (partialExpansion Y g N) Z r * ((r ^ m : ℝ) : ℂ))
        =ᵐ[ν] (fun _ ↦ 0) := by
      filter_upwards [ae_radial_mem n a b] with r hr
      simp [h r hr, hk]
    rw [integral_congr_ae hzero, integral_zero]

end Runcorn
