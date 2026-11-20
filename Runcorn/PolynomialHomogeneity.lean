module

public import Runcorn.PolynomialCalculus

/-! # Radial homogeneity of polynomial evaluation -/
@[expose] public section
noncomputable section
open MvPolynomial
namespace Runcorn
variable {n : ℕ}

theorem polynomialValue_smul_of_homogeneous (P : Polynomial.Poly n) {k : ℕ}
    (hP : P.IsHomogeneous k) (t : ℝ) (x : Space n) :
    polynomialValue P (t • x) = (t : ℂ)^k * polynomialValue P x := by
  unfold polynomialValue
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [eval_monomial, Finsupp.prod, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hP.degree_eq_sum_deg_support ha]
  ring

end Runcorn
