module

public import Runcorn.PolynomialCalculus
public import Runcorn.SpecialPair

/-!
# Gradient products of solid spherical harmonics

In Lemma 5 of arXiv:2607.18379v1 we first extract the common radial power from
the product of gradients. Euler's identity then gives the polynomial numerator
of `Runcorn.Polynomial.gradientNumerator_expansion`.
-/

@[expose] public section
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace Runcorn
variable {n : ℕ}
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

/-- Kelvin transform of a homogeneous polynomial of degree `q`, evaluated away from zero. -/
def kelvinMode (q : ℕ) (Q : Polynomial.Poly n) (x : Space n) : ℂ :=
  (‖x‖ ^ (2 - (n : ℤ) - 2*q) : ℝ) * polynomialValue Q x

theorem polynomialValue_radiusSq (x : Space n) :
    polynomialValue (Polynomial.radiusSq n) x = (‖x‖ : ℂ)^2 := by
  simp [Polynomial.radiusSq, polynomialValue, EuclideanSpace.real_norm_sq_eq, ← Complex.ofReal_pow,
    ← Complex.ofReal_sum]

theorem gradDot_kelvinMode (p q : ℕ) (P Q : Polynomial.Poly n) (hp : P.IsHomogeneous p)
    {x : Space n} (hx : x ≠ 0) :
    gradDot (polynomialValue P) (kelvinMode q Q) x =
      (‖x‖ ^ (-(n : ℤ) - 2*q) : ℝ) * polynomialValue (Polynomial.gradientNumerator p q P Q) x := by
  let s : ℤ := 2 - n - 2*q
  let R : ℂ := (‖x‖ ^ (-(n : ℤ) - 2*q) : ℝ)
  have hs : s-2 = -(n : ℤ)-2*q := by dsimp [s]; omega
  have hfac : ((‖x‖ ^ s : ℝ) : ℂ) = R * (‖x‖ : ℂ)^2 := by
    rw [show s = (-(n : ℤ) - 2*q) + 2 by dsimp [s]; omega,
      zpow_add₀ (norm_ne_zero_iff.mpr hx)]
    simp [R]
  have hE : (∑ i, (x i : ℂ) * polynomialValue (pderiv i P) x) =
      (p : ℂ) * polynomialValue P x := by
    have he := congrArg (eval (fun i => (x i : ℂ))) hp.sum_X_mul_pderiv
    simpa [polynomialValue, nsmul_eq_mul] using he
  have hd (i : Fin n) : fderiv ℝ (kelvinMode q Q) x (e i) =
      R * (‖x‖ : ℂ)^2 * polynomialValue (pderiv i Q) x +
      polynomialValue Q x * ((s : ℂ) * R * (x i : ℂ)) := by
    unfold kelvinMode
    rw [fderiv_fun_mul (SpecialPair.radial_differentiable s hx)
      ((contDiff_polynomialValue Q 1).differentiable (by decide) x)]
    simp only [add_apply, smul_apply, smul_eq_mul, polynomialValue_partial]
    rw [SpecialPair.radial_derivative s hx i, hs, ← hfac]
  calc
    _ = (R * (‖x‖ : ℂ)^2) * (∑ i, polynomialValue (pderiv i P) x * polynomialValue (pderiv i Q) x) +
        (R * (s : ℂ) * polynomialValue Q x) *
          ∑ i, (x i : ℂ) * polynomialValue (pderiv i P) x := by
      simp only [gradDot, polynomialValue_partial, hd, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [hE]
      simp only [Polynomial.gradientNumerator, Polynomial.gradDot, polynomialValue, map_add, map_mul,
        map_sum, eval_C]
      change _ = R * (_ + polynomialValue (Polynomial.radiusSq n) x * _)
      rw [polynomialValue_radiusSq]
      dsimp [s]
      push_cast
      ring

/-- Pointwise expansion for the gradient product with its exact scalar coefficients,
including zeros at the endpoints as characterized by
`Polynomial.gradientCoefficient_eq_zero_iff`. -/
theorem gradDot_kelvinMode_expansion (hn : 2 ≤ n) (p q : ℕ) (P Q : Polynomial.Poly n)
    (hp : P.IsHomogeneous p) (hq : Q.IsHomogeneous q)
    (hP : Polynomial.lap P = 0) (hQ : Polynomial.lap Q = 0) :
    ∃ H : ℕ → Polynomial.Poly n,
      (∀ l ≤ min p q, (H l).IsHomogeneous (p+q-2*l) ∧ Polynomial.lap (H l) = 0) ∧
      ∀ x : Space n, x ≠ 0 → gradDot (polynomialValue P) (kelvinMode q Q) x =
        ∑ l ∈ Finset.range (min p q + 1),
          (-((p : ℂ)-l) * ((n : ℂ)-2+2*q-2*l)) *
          (‖x‖ ^ (-(n : ℤ)-2*q+2*l) : ℝ) * polynomialValue (H l) x := by
  obtain ⟨H,hH,he⟩ := Polynomial.gradientNumerator_expansion (by omega) p q P Q hp hq hP hQ
  refine ⟨H,hH,?_⟩
  intro x hx
  rw [gradDot_kelvinMode _ _ _ _ hp hx, he]
  simp only [polynomialValue, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [map_mul, map_pow, eval_C]
  change _ * (_ * (polynomialValue (Polynomial.radiusSq n) x ^ l * _)) = _
  rw [polynomialValue_radiusSq, zpow_add₀ (norm_ne_zero_iff.mpr hx)]
  push_cast
  rw [show (2 : ℤ)*l = ((2*l : ℕ) : ℤ) by simp, zpow_natCast, pow_mul]
  ring

/-- Lemma 5(a,b) with the source's two sharp upper limits. The harmonic
polynomials absorbing the scalar coefficients are independent of `x`. -/
theorem gradDot_kelvinMode_truncated (hn : 2 ≤ n) (p q : ℕ) (hpPos : 1 ≤ p)
    (_hqPos : n = 2 → 1 ≤ q) (P Q : Polynomial.Poly n)
    (hp : P.IsHomogeneous p) (hq : Q.IsHomogeneous q)
    (hP : Polynomial.lap P = 0) (hQ : Polynomial.lap Q = 0) :
    let bound := if n = 2 then min (p-1) (q-1) else min (p-1) q
    ∃ H : ℕ → Polynomial.Poly n,
      (∀ l ≤ bound, (H l).IsHomogeneous (p+q-2*l) ∧ Polynomial.lap (H l) = 0) ∧
      ∀ x : Space n, x ≠ 0 → gradDot (polynomialValue P) (kelvinMode q Q) x =
        ∑ l ∈ Finset.range (bound + 1),
          (‖x‖ ^ (-(n : ℤ)-2*q+2*l) : ℝ) * polynomialValue (H l) x := by
  let b := if n = 2 then min (p-1) (q-1) else min (p-1) q
  let c := fun l : ℕ => -((p : ℂ)-l) * ((n : ℂ)-2+2*q-2*l)
  have hbm : b ≤ min p q := by dsimp [b]; split <;> omega
  obtain ⟨K, hK, he⟩ := gradDot_kelvinMode_expansion hn p q P Q hp hq hP hQ
  refine ⟨fun l => C (c l) * K l, ?_, ?_⟩
  · intro l hl
    obtain ⟨ha,hb⟩ := hK l (hl.trans hbm)
    exact ⟨ha.C_mul _, by rw [Polynomial.lap_const_mul, hb, mul_zero]⟩
  · intro x hx
    rw [he x hx]
    let F := fun l : ℕ => c l * (‖x‖ ^ (-(n : ℤ)-2*q+2*l) : ℝ) * polynomialValue (K l) x
    change (∑ l ∈ Finset.range (min p q + 1), F l) = _
    have hsub : Finset.range (b+1) ⊆ Finset.range (min p q+1) :=
      Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro l _
      simp only [F, polynomialValue, map_mul, eval_C]
      ring
    · intro l hL hU
      have hl : l ≤ min p q := by simpa using hL
      have hu : b < l := by simpa using hU
      have hz : c l = 0 :=
        (Polynomial.gradientCoefficient_eq_zero_iff hn hl).mpr (by dsimp [b] at hu; split at hu <;> omega)
      simp [F, hz]

end Runcorn
