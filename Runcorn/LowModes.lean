module

public import Runcorn.Definitions
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-! # The surviving low-degree angular modes in Theorem 1 -/

open Set Filter Topology
@[expose] public section

noncomputable section
namespace Runcorn

/-- Restrictions of homogeneous harmonic polynomials of degree zero are constants. -/
theorem degree_zero_is_constant {n : ℕ} {Y : Sphere n → ℂ}
    (hY : IsSphericalHarmonic 0 Y) : ∃ c : ℂ, ∀ σ, Y σ = c := by
  obtain ⟨P, hP, _, h⟩ := hY
  refine ⟨P.coeff 0, fun σ ↦ ?_⟩
  rw [h σ]
  unfold polynomialValue
  have hp := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin n)).mpr hP)
  conv_lhs => rw [hp]
  simp

/-- The degree-one restrictions are linear combinations of the coordinate
functions on the sphere. This applies to any of the bases in Theorem 2. -/
theorem degree_one_is_linear {n : ℕ} {Y : Sphere n → ℂ} (hY : IsSphericalHarmonic 1 Y) :
    ∃ c : Fin n → ℂ, ∀ σ : Sphere n, Y σ = ∑ i, c i * ((σ.val i : ℝ) : ℂ) := by
  obtain ⟨P, hP, _, h⟩ := hY
  let c : Fin n → ℂ := fun i ↦ (MvPolynomial.pderiv i P).coeff 0
  refine ⟨c, fun σ ↦ ?_⟩
  have hpart (i : Fin n) : MvPolynomial.pderiv i P = MvPolynomial.C (c i) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin n)).mpr (hP.pderiv (i := i)))
  have he : (∑ i : Fin n, MvPolynomial.X i * MvPolynomial.pderiv i P) = P := by
    simpa using hP.sum_X_mul_pderiv
  rw [h σ]
  unfold polynomialValue
  conv_lhs => rw [← he]
  simp [map_sum, hpart, mul_comm]

/-- Convert constants and linear circle modes to precisely the exponential
parameterization used in Theorem 1(iii). -/
theorem threeModes_of_cos_sin {n : ℕ} {lo hi : ℝ} {f : Space n → ℂ}
    {c A B : ℝ → ℂ} (hc : ContinuousOn c (Ioo lo hi))
    (hA : ContinuousOn A (Ioo lo hi)) (hB : ContinuousOn B (Ioo lo hi))
    (hf : ∀ r ∈ Ioo lo hi, ∀ φ : ℝ, f (polarPoint n r φ) =
      c r + A r * (Real.cos φ : ℂ) + B r * (Real.sin φ : ℂ)) :
    ThreeModes lo hi f := by
  refine ⟨fun r ↦ (A r + B r * Complex.I) / 2, c, fun r ↦ (A r - B r * Complex.I) / 2,
    (hA.add (hB.mul continuousOn_const)).div_const _, hc,
    (hA.sub (hB.mul continuousOn_const)).div_const _, ?_⟩
  intro r hr φ
  have hePos : Complex.exp (Complex.I * (φ : ℂ)) =
      (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_ofReal_mul_I]
  have heNeg : Complex.exp (-Complex.I * (φ : ℂ)) =
      (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I := by
    rw [show -Complex.I * (φ : ℂ) = (-φ : ℝ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  rw [hf r hr φ, hePos, heNeg]
  linear_combination (B r * Real.sin φ) * Complex.I_sq

/-- A pointwise expansion consisting only of degree-zero harmonics is radial. -/
theorem radialOn_of_degree_zero {n : ℕ} {lo hi : ℝ} (hlo : 0 < lo) {f : Space n → ℂ}
    (Y : AngularFamily n) (hY : IsAngularBasis Y) (g : Coefficients n)
    (hf : ∀ r ∈ Ioo lo hi, ∀ σ : Sphere n, f (r • σ.val) = ∑ j, g 0 j r * Y 0 j σ) :
    RadialOn lo hi f := by
  choose c hc using fun j => degree_zero_is_constant ((hY 0).1 j)
  refine ⟨fun r => ∑ j, g 0 j r * c j, fun x hx => ?_⟩
  have hnorm : 0 < ‖x‖ := hlo.trans hx.1
  let σ : Sphere n := ⟨‖x‖⁻¹ • x, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm),
      inv_mul_cancel₀ hnorm.ne']⟩
  have he : ‖x‖ • σ.val = x := by
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
  simpa only [he, hc] using hf ‖x‖ hx σ

/-- The polar-angle parametrization of the unit circle. -/
def circleDirection (φ : ℝ) : Sphere 2 :=
  ⟨polarPoint 2 1 φ, by
    rw [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, polarPoint, Real.cos_sq_add_sin_sq]⟩

/-- On the circle, arbitrary degree-zero and degree-one harmonics with
continuous radial coefficients give the three modes of the varying-shell theorem. -/
theorem threeModes_of_degrees_zero_one {lo hi : ℝ} {f : Space 2 → ℂ}
    (Y : AngularFamily 2) (hY : IsAngularBasis Y) (g : Coefficients 2)
    (h0 : ∀ j, ContinuousOn (g 0 j) (Ioo lo hi))
    (h1 : ∀ j, ContinuousOn (g 1 j) (Ioo lo hi))
    (hf : ∀ r ∈ Ioo lo hi, ∀ σ : Sphere 2, f (r • σ.val) =
      (∑ j, g 0 j r * Y 0 j σ) + ∑ j, g 1 j r * Y 1 j σ) :
    ThreeModes lo hi f := by
  choose c hc using fun j => degree_zero_is_constant ((hY 0).1 j)
  choose b hb using fun j => degree_one_is_linear ((hY 1).1 j)
  apply threeModes_of_cos_sin
    (c := fun r => ∑ j, g 0 j r * c j)
    (A := fun r => ∑ j, g 1 j r * b j 0)
    (B := fun r => ∑ j, g 1 j r * b j 1)
  · exact continuousOn_finsetSum _ fun j _ => (h0 j).mul continuousOn_const
  · exact continuousOn_finsetSum _ fun j _ => (h1 j).mul continuousOn_const
  · exact continuousOn_finsetSum _ fun j _ => (h1 j).mul continuousOn_const
  · intro r hr φ
    have he : r • (circleDirection φ).val = polarPoint 2 r φ := by
      ext i
      fin_cases i <;> simp [circleDirection, polarPoint]
    rw [← he, hf r hr]
    simp [hc, hb, circleDirection, polarPoint, Fin.sum_univ_two, mul_add, Finset.sum_add_distrib,
      Finset.sum_mul, mul_assoc, add_assoc]

end Runcorn
