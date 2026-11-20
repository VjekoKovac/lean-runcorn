module

public import Runcorn.Series
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# L² convergence for a radial field of spherical slices

For a square-integrable field of spherical slices the angular coefficients are
square-integrable in the radial variable. The integral of the squared angular
error tends to zero. This is the product-space step of the annular expansion.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace Runcorn

/-- A coordinate functional on angular L² sends a radial L² field to a radial L² function. -/
theorem angularCoefficient_memLp {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    {μ : Measure ℝ} {F : ℝ → AngularL2 n} (hF : MemLp F 2 μ) (a : Mode n) :
    MemLp (fun r ↦ angularCoefficient Y (F r) a) 2 μ := by
  have h := hF.continuousLinearMap_comp (innerSL ℂ (angularVector Y hY a))
  simpa only [angularCoefficient, ← angularVector_inner Y hY, ← angularVector_inner_basis Y hY,
    div_eq_inv_mul, Function.comp_def, innerSL_apply_apply] using
    h.const_mul (inner ℂ (angularVector Y hY a) (angularVector Y hY a))⁻¹

/-- Squared-distance bound for projection onto finitely many unnormalized, mutually
orthogonal vectors. The proof is the Pythagorean identity for the residual. -/
theorem orthogonal_partial_error_le {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (w : ι → H) (hne : ∀ i, w i ≠ 0)
    (hortho : Pairwise (fun i j ↦ inner ℂ (w i) (w j) = 0)) (s : Finset ι) (x : H) :
    ‖(∑ i ∈ s, (inner ℂ (w i) x / inner ℂ (w i) (w i)) • w i) - x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  classical
  let c := fun i ↦ inner ℂ (w i) x / inner ℂ (w i) (w i)
  let z := ∑ i ∈ s, c i • w i
  have hres (i : ι) (hi : i ∈ s) : inner ℂ (w i) (x - z) = 0 := by
    rw [inner_sub_right, sub_eq_zero]
    change inner ℂ (w i) x = inner ℂ (w i) (∑ j ∈ s, c j • w j)
    rw [inner_sum]
    simp_rw [inner_smul_right]
    rw [Finset.sum_eq_single_of_mem i hi (fun j _ hji ↦ by rw [hortho hji.symm, mul_zero])]
    have hself : inner ℂ (w i) (w i) ≠ 0 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp [hne i]
    exact (div_mul_cancel₀ _ hself).symm
  have hz : inner ℂ z (x - z) = 0 := by
    change inner ℂ (∑ i ∈ s, c i • w i) (x - z) = 0
    rw [sum_inner]
    exact Finset.sum_eq_zero (fun i hi ↦ by rw [inner_smul_left, hres i hi, mul_zero])
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero z (x - z) hz
  rw [add_sub_cancel] at hpy
  change ‖z - x‖ ^ 2 ≤ ‖x‖ ^ 2
  rw [norm_sub_rev]
  linarith [sq_nonneg ‖z‖]

/-- Partial angular expansion of a field at the radius supplied to it. -/
def angularPartial {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (N : ℕ) (x : AngularL2 n) : AngularL2 n :=
  ∑ k ∈ Finset.range N, ∑ j : Fin (harmonicDimension n k),
    angularCoefficient Y x ⟨k,j⟩ • angularVector Y hY ⟨k,j⟩

private theorem angularPartial_continuous {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (N : ℕ) : Continuous (angularPartial Y hY N) := by
  unfold angularPartial
  apply continuous_finsetSum
  intro k _
  apply continuous_finsetSum
  intro j _
  have hc : Continuous (fun x : AngularL2 n ↦
      angularCoefficient Y x ⟨k,j⟩) := by
    simp_rw [angularCoefficient, ← angularVector_inner Y hY ⟨k,j⟩]
    exact (continuous_const.inner continuous_id).div_const _
  exact hc.smul continuous_const

/-- Integrating the squared angular error of the degree-ordered expansion against the radial
measure gives a quantity tending to zero, for every square-integrable field of slices.
In particular μ can be radialMeasure n a b. -/
theorem radial_integrated_angular_error {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (hcross : ∀ a b : Mode n, a.1 ≠ b.1 →
      (∫ σ, Y b.1 b.2 σ * conj (Y a.1 a.2 σ) ∂surfaceMeasure n) = 0)
    (hdense : (Submodule.span ℂ (Set.range (angularVector Y hY))).topologicalClosure = ⊤)
    {μ : Measure ℝ} (F : ℝ → AngularL2 n) (hF : MemLp F 2 μ) :
    Tendsto (fun N : ℕ ↦ ∫ r, ‖angularPartial Y hY N (F r) - F r‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  classical
  have horth : Pairwise (fun a b : Mode n ↦
      inner ℂ (angularVector Y hY a) (angularVector Y hY b) = 0) := by
    rintro ⟨k,i⟩ ⟨l,j⟩ hne
    rw [angularVector_inner_basis]
    by_cases hkl : k = l
    · subst l
      exact (hY k).2.2.2 j i (fun hji ↦ hne (by cases hji; rfl))
    · exact hcross ⟨k,i⟩ ⟨l,j⟩ hkl
  have hbound (N : ℕ) (r : ℝ) : ‖angularPartial Y hY N (F r) - F r‖ ^ 2 ≤ ‖F r‖ ^ 2 := by
    let s : Finset (Mode n) := (Finset.range N).sigma (fun _ ↦ Finset.univ)
    have h := orthogonal_partial_error_le (angularVector Y hY) (angularVector_ne_zero Y hY)
      horth s (F r)
    simp_rw [angularVector_inner_basis, angularVector_inner] at h
    simpa only [s, Finset.sum_sigma, angularCoefficient, angularPartial] using h
  have hm (N : ℕ) : AEStronglyMeasurable
      (fun r ↦ ‖angularPartial Y hY N (F r) - F r‖ ^ 2) μ := by
    exact (((angularPartial_continuous Y hY N).sub continuous_id).norm.pow 2).comp_aestronglyMeasurable
      hF.aestronglyMeasurable
  have hlim (r : ℝ) :
      Tendsto (fun N ↦ ‖angularPartial Y hY N (F r) - F r‖ ^ 2) atTop (𝓝 0) := by
    simpa [angularPartial] using (((angular_degree_sums_tendsto Y hY hcross hdense (F r)).sub_const (F r)).norm.pow 2)
  simpa using tendsto_integral_of_dominated_convergence (fun r ↦ ‖F r‖ ^ 2) hm
    (hF.integrable_norm_pow (by decide : 2 ≠ 0))
    (fun N ↦ Filter.Eventually.of_forall (fun r ↦ by simpa using hbound N r))
    (Filter.Eventually.of_forall hlim)

end Runcorn
