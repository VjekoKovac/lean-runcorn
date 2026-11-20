module

public import Runcorn.PolynomialCalculus
public import Runcorn.SpecialPair

/-! # Radially weighted solid harmonics

This proves formula (2.8) of Kovač and Smolić for integer exponents,
including every Kelvin exponent used in Lemmas 4 and 5.
-/

@[expose] public section
noncomputable section
open Filter MvPolynomial InnerProductSpace Laplacian
open scoped Topology
namespace Runcorn
variable {n : ℕ}
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

/-- The function rˢP(x), evaluated on real Euclidean space. -/
def weightedPoly (s : ℤ) (P : Polynomial.Poly n) (x : Space n) : ℂ :=
  ((‖x‖ ^ s : ℝ) : ℂ) * polynomialValue P x

theorem contDiffAt_weightedPoly (s : ℤ) (P : Polynomial.Poly n) {x : Space n}
    (hx : x ≠ 0) : ContDiffAt ℝ 2 (weightedPoly s P) x := by
  have hr : ContDiffAt ℝ 2 (fun y : Space n => ‖y‖ ^ s) x := by
    cases s with
    | ofNat m => simpa using (contDiffAt_norm ℝ hx (n := 2)).pow m
    | negSucc m =>
      have hd := ((contDiffAt_norm ℝ hx (n := 2)).pow (m+1)).inv
        (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))
      convert! hd using 1
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x hr).mul
    (contDiff_polynomialValue P 2).contDiffAt

theorem weightedPoly_partial (s : ℤ) (P : Polynomial.Poly n) (i : Fin n) {x : Space n}
    (hx : x ≠ 0) :
    fderiv ℝ (weightedPoly s P) x (e i) =
      weightedPoly s (pderiv i P) x + s * weightedPoly (s-2) (X i * P) x := by
  have hP := (contDiff_polynomialValue P 1).differentiable (by decide) x
  unfold weightedPoly
  rw [fderiv_fun_mul (SpecialPair.radial_differentiable s hx) hP]
  simp only [add_apply, smul_apply, smul_eq_mul, SpecialPair.radial_derivative s hx i,
    polynomialValue_partial, polynomialValue, map_mul, eval_X]
  ring

private theorem weightedPoly_partial_twice (s : ℤ) (P : Polynomial.Poly n) (i : Fin n)
    {x : Space n} (hx : x ≠ 0) :
    fderiv ℝ (fun y => fderiv ℝ (weightedPoly s P) y (e i)) x (e i) =
      weightedPoly s (pderiv i (pderiv i P)) x +
      s * weightedPoly (s-2) P x +
      (2*s) * weightedPoly (s-2) (X i * pderiv i P) x +
      (s*(s-2)) * weightedPoly (s-4) (X i ^ 2 * P) x := by
  have hh : (fun y => fderiv ℝ (weightedPoly s P) y (e i)) =ᶠ[𝓝 x]
      (fun y => weightedPoly s (pderiv i P) y + s * weightedPoly (s-2) (X i * P) y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy using weightedPoly_partial s P i hy
  have diff (t : ℤ) (Q : Polynomial.Poly n) :=
    (contDiffAt_weightedPoly t Q hx).differentiableAt (by decide)
  rw [hh.fderiv_eq, fderiv_fun_add (diff _ _) ((diff _ _).const_mul (s : ℂ)),
      fderiv_const_mul (diff _ _) (s : ℂ)]
  simp only [add_apply, smul_apply, smul_eq_mul, weightedPoly_partial _ _ _ hx,
    show s-2-2 = s-4 by omega, pderiv_mul, pderiv_X_self, one_mul, weightedPoly, polynomialValue,
    map_add, map_mul, map_pow, eval_X, Int.cast_sub, Int.cast_ofNat]
  ring

/-- The radial Laplacian formula for a harmonic homogeneous polynomial, including
negative integer exponents. -/
theorem laplacian_weighted_harmonic (s : ℤ) {k : ℕ} (P : Polynomial.Poly n)
    (hP : P.IsHomogeneous k) (hΔ : Polynomial.lap P = 0) {x : Space n} (hx : x ≠ 0) :
    Δ (weightedPoly s P) x = s * (s + 2 * (k : ℂ) + n - 2) * weightedPoly (s-2) P x := by
  rw [laplacian_eq_sum_partials (contDiffAt_weightedPoly s P hx)]
  simp_rw [weightedPoly_partial_twice s P _ hx]
  let v := MvPolynomial.eval (fun i => (x i : ℂ))
  have he : ∑ i, v (X i * pderiv i P) = k * v P := by
    simpa [map_sum, nsmul_eq_mul] using congrArg v hP.sum_X_mul_pderiv
  have hl : ∑ i, v (pderiv i (pderiv i P)) = 0 := by
    simpa [Polynomial.lap, map_sum] using congrArg v hΔ
  have hr : ∑ i, v (X i ^ 2 * P) = ((‖x‖ ^ 2 : ℝ) : ℂ) * v P := by
    simp only [map_mul, map_pow, ← Finset.sum_mul]
    simp only [v, eval_X]
    rw [EuclideanSpace.real_norm_sq_eq]
    push_cast
    rfl
  have hrpow : (‖x‖ ^ (s-4) : ℝ) * ‖x‖ ^ 2 = ‖x‖ ^ (s-2) := by
    rw [← zpow_natCast ‖x‖ 2, ← zpow_add₀ (norm_ne_zero_iff.mpr hx)]
    congr 1; omega
  have hrC := congrArg Complex.ofReal hrpow
  push_cast at hrC
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, weightedPoly, polynomialValue]
  simp only [← show v = MvPolynomial.eval (fun i => (x i : ℂ)) by rfl,
    he, hl, hr, mul_zero, zero_add, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  linear_combination (norm := ring_nf) (s : ℂ)*(s-2)*v P*hrC

/-- The homogeneous Kelvin transform is harmonic away from zero. -/
theorem kelvin_harmonicOn {k : ℕ} (P : Polynomial.Poly n)
    (hP : P.IsHomogeneous k) (hΔ : Polynomial.lap P = 0) :
    HarmonicOnNhd (weightedPoly (2-(n:ℤ)-2*k) P) {x | x ≠ 0} := by
  intro x hx
  refine ⟨contDiffAt_weightedPoly _ _ hx, ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  rw [laplacian_weighted_harmonic _ P hP hΔ hy]
  push_cast
  change _ = (0 : ℂ)
  ring

end Runcorn
