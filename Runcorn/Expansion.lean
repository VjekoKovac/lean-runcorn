module

public import Runcorn.Definitions
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Finite spherical harmonic expansions

The partial sums in Theorem 2 are functions on the ambient annulus. Evaluation at
a polar point recovers the finite sums in (1.3). The last lemma computes the
angular pairing of one whole degree with one element of its orthogonal basis.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Runcorn

/-- Distance from the origin in positive-radius polar coordinates. -/
theorem norm_polarPoint_of_sphere {n : ℕ} (r : ℝ) (hr : 0 < r) (σ : Sphere n) :
    ‖r • (σ : Space n)‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere σ, mul_one]

/-- Normalizing a positive multiple of a unit vector recovers its direction. -/
theorem atDirection_smul {n : ℕ} (Y : Sphere n → ℂ) (r : ℝ) (hr : 0 < r) (σ : Sphere n) :
    atDirection Y (r • (σ : Space n)) = Y σ := by
  have hdir : ‖r • (σ : Space n)‖⁻¹ • (r • (σ : Space n)) = σ.val := by
    rw [norm_polarPoint_of_sphere r hr σ, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  simp [atDirection, hdir]

/-- The ambient definition evaluated at a polar point is exactly the paper’s finite sum. -/
theorem partialExpansion_polar {n : ℕ} (Y : AngularFamily n) (g : Coefficients n)
    (N : ℕ) (r : ℝ) (hr : 0 < r) (σ : Sphere n) :
    partialExpansion Y g N (r • (σ : Space n)) =
      ∑ k ∈ Finset.range N, ∑ j : Fin (harmonicDimension n k), g k j r * Y k j σ := by
  simp only [partialExpansion, norm_polarPoint_of_sphere r hr σ, atDirection_smul _ r hr σ]

/-- Spherical harmonics are continuous on the unit sphere. -/
theorem IsSphericalHarmonic.continuous {n k : ℕ} {Y : Sphere n → ℂ}
    (hY : IsSphericalHarmonic k Y) : Continuous Y := by
  obtain ⟨P, _, hP, hY⟩ := hY
  have hcont : Continuous (polynomialValue P) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hP x (Set.mem_univ x)).1.continuousAt
  exact (hcont.comp continuous_subtype_val).congr fun σ ↦ (hY σ).symm

/-- Pairing a finite expansion of degree k with a basis vector picks out its
coefficient times the squared norm of that vector. This handles unnormalized bases. -/
theorem angularProjection_degree {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (k : ℕ) (c : Fin (harmonicDimension n k) → ℂ) (j : Fin (harmonicDimension n k)) :
    (∫ σ : Sphere n, (∑ i, c i * Y k i σ) * conj (Y k j σ) ∂surfaceMeasure n) =
      c j * (∫ σ : Sphere n, Y k j σ * conj (Y k j σ) ∂surfaceMeasure n) := by
  classical
  have hf (i : Fin (harmonicDimension n k)) :
      Integrable (fun σ : Sphere n ↦ c i * (Y k i σ * conj (Y k j σ))) (surfaceMeasure n) := by
    have hc : Continuous (fun σ : Sphere n ↦ c i * (Y k i σ * conj (Y k j σ))) :=
      continuous_const.mul (((hY k).1 i).continuous.mul
        (Complex.continuous_conj.comp ((hY k).1 j).continuous))
    unfold surfaceMeasure
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ ↦ hf i)]
  simp_rw [integral_const_mul]
  apply Finset.sum_eq_single j
  · intro i _ hij
    rw [(hY k).2.2.2 i j hij, mul_zero]
  · simp

/-- A vector in the specified orthogonal angular basis has nonzero squared L² norm. -/
theorem angularMass_ne_zero {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (k : ℕ) (j : Fin (harmonicDimension n k)) :
    (∫ σ : Sphere n, Y k j σ * conj (Y k j σ) ∂surfaceMeasure n) ≠ 0 := by
  have hc := ((hY k).1 j).continuous
  have hc₂ : Continuous (fun σ ↦ ‖Y k j σ‖ ^ 2) := hc.norm.pow 2
  have hi : Integrable (fun σ ↦ ‖Y k j σ‖ ^ 2) (surfaceMeasure n) := by
    unfold surfaceMeasure
    exact hc₂.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  intro h
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hae := (integral_eq_zero_iff_of_nonneg (fun σ ↦ sq_nonneg ‖Y k j σ‖) hi).1 h
  have hzero : (fun σ ↦ ‖Y k j σ‖ ^ 2) = 0 := by
    unfold surfaceMeasure at hae
    exact Measure.eq_of_ae_eq hae hc₂ continuous_zero
  apply (hY k).2.1.ne_zero j
  funext σ
  have hz := congrFun hzero σ
  simpa using hz

/-- For a homogeneous finite expansion, dividing the angular pairing by its mass
recovers the coefficient, in the normalization of equation (1.4). -/
theorem coefficient_degree {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (k : ℕ) (c : Fin (harmonicDimension n k) → ℂ) (j : Fin (harmonicDimension n k)) :
    (∫ σ : Sphere n, (∑ i, c i * Y k i σ) * conj (Y k j σ) ∂surfaceMeasure n) /
      (∫ σ : Sphere n, Y k j σ * conj (Y k j σ) ∂surfaceMeasure n) = c j := by
  rw [angularProjection_degree Y hY, mul_div_cancel_right₀ _ (angularMass_ne_zero Y hY k j)]

end Runcorn
