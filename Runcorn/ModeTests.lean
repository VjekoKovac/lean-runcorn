module

public import Runcorn.GradientDecomposition
public import Runcorn.Separated
public import Runcorn.PolynomialHomogeneity

/-! # Sufficiency for homogeneous interior and exterior tests
Each term of the gradient expansion separates into one angular harmonic and
one of exactly the Laurent powers occurring in Theorem 2.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set MvPolynomial
namespace Runcorn
variable {n : ℕ}

theorem polynomialValue_atDirection (P : Polynomial.Poly n) {k : ℕ} (hP : P.IsHomogeneous k)
    {x : Space n} (hx : x ≠ 0) :
    polynomialValue P x = (‖x‖ : ℂ)^k * atDirection (fun σ : Sphere n => polynomialValue P σ.val) x := by
  have hr := norm_pos_iff.mpr hx
  have hσ : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Space n) 1 := by simp [norm_smul, hr.ne']
  simp only [atDirection, dite_eq_left hσ, polynomialValue_smul_of_homogeneous P hP, Complex.ofReal_inv,
    inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero k (Complex.ofReal_ne_zero.mpr hr.ne')), one_mul]

/-- All separated moment equalities imply the Runcorn integral for each pair
of homogeneous harmonic polynomials, the exterior one Kelvin transformed. -/
theorem homogeneous_test_zero_of_separated {n : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (ha : 0 < a) {f : Space n → ℂ} (hf : MemLp f 2 (volume.restrict (annulus a b)))
    (hmom : ∀ (k : ℕ) (Y : Sphere n → ℂ), IsSphericalHarmonic k Y →
      ∀ m : ℤ, momentExponent n k m →
        (∫ x in annulus a b, f x * atDirection Y x * ((‖x‖^m : ℝ) : ℂ)) = 0)
    (p q : ℕ) (hpos : 1 ≤ p) (hqpos : n = 2 → 1 ≤ q) (P Q : Polynomial.Poly n)
    (hp : P.IsHomogeneous p) (hq : Q.IsHomogeneous q)
    (hP : Polynomial.lap P = 0) (hQ : Polynomial.lap Q = 0) :
    (∫ x in annulus a b, f x * gradDot (polynomialValue P) (kelvinMode q Q) x) = 0 := by
  let B := if n = 2 then min (p-1) (q-1) else min (p-1) q
  let m : ℤ := (p : ℤ) - q - n
  obtain ⟨H,hH,he⟩ := gradDot_kelvinMode_truncated hn p q hpos hqpos P Q hp hq hP hQ
  let Y := fun l (σ : Sphere n) => polynomialValue (H l) σ.val
  have hh (l : ℕ) (hl : l ≤ B) : IsSphericalHarmonic (p+q-2*l) (Y l) :=
    ⟨H l, (hH l hl).1, harmonic_polynomialValue _ (hH l hl).2, fun _ => rfl⟩
  have hm (l : ℕ) (hl : l ≤ B) : momentExponent n (p+q-2*l) m := by
    apply momentExponent_of_gradient_indices hn
    all_goals dsimp [B] at hl; split at hl <;> omega
  let F := fun l (x : Space n) => f x * atDirection (Y l) x * ((‖x‖ ^ m : ℝ) : ℂ)
  have hint (l : ℕ) (hl : l ∈ Finset.range (B+1)) : IntegrableOn (F l) (annulus a b) :=
    integrableOn_separatedTest ha hf (hh l (by simpa using hl)).continuous _
  calc
    _ = ∫ x in annulus a b, ∑ l ∈ Finset.range (B+1), F l x := by
      apply setIntegral_congr_fun (isCompact_annulus a b).measurableSet
      intro x hx
      have h0 : x ≠ 0 := norm_pos_iff.mp (ha.trans_le hx.1)
      dsimp only
      rw [he x h0, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      have hl' : l ≤ B := by simpa using hl
      have hdeg : 2*l ≤ p+q := by dsimp [B] at hl'; split at hl' <;> omega
      rw [polynomialValue_atDirection (H l) (hH l hl').1 h0]
      dsimp only [F,Y]
      have hr : (‖x‖ : ℂ) ^ m =
          (‖x‖ : ℂ)^(-(n : ℤ)-2*q+2*l) * (‖x‖ : ℂ)^(p+q-2*l) := by
        rw [← zpow_natCast, ← zpow_add₀ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0))]
        congr 1
        dsimp [m]
        omega
      rw [Complex.ofReal_zpow, Complex.ofReal_zpow, hr]
      ring
    _ = 0 := by
      rw [integral_finsetSum _ hint]
      apply Finset.sum_eq_zero
      intro l hl
      exact hmom _ _ (hh l (by simpa using hl)) _ (hm l (by simpa using hl))

end Runcorn
