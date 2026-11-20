module

public import Runcorn.Algebra
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Fischer pairing

The paper uses a Hermitian pairing on homogeneous polynomials. Here we use its
complex bilinear version and algebraic duality. This avoids any normalization of
vectors and retains the same factorial weights and Laplacian adjoint identity.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace Runcorn.Polynomial
variable {n : ℕ}

/-- The product of the factorials of the coordinate exponents. -/
def multiFactor (a : Fin n →₀ ℕ) : ℕ := ∏ i, (a i).factorial

private theorem multiFactor_add_single (a : Fin n →₀ ℕ) (i : Fin n) :
    multiFactor (a + Finsupp.single i 1) = (a i + 1) * multiFactor a := by
  classical
  unfold multiFactor
  have he (j : Fin n) : ((a + Finsupp.single i 1 : Fin n →₀ ℕ) j).factorial =
      (if i = j then a i + 1 else 1) * (a j).factorial := by
    by_cases h : i = j
    · subst j; simp [Nat.factorial_succ]
    · simp [h]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

/-- Linear in its second argument. -/
def fischerPair (H : Poly n) : Poly n →ₗ[ℂ] ℂ :=
  (Finsupp.linearCombination ℂ fun a => (multiFactor a : ℂ) * H.coeff a).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem fischerPair_sum (H Q : Poly n) :
    fischerPair H Q = ∑ a ∈ Q.support, Q.coeff a * ((multiFactor a : ℂ) * H.coeff a) :=
  rfl

private theorem fischerPair_monomial (H : Poly n) (a : Fin n →₀ ℕ) (c : ℂ) :
    fischerPair H (monomial a c) = c * ((multiFactor a : ℂ) * H.coeff a) := by
  change Finsupp.linearCombination ℂ (fun b => (multiFactor b : ℂ) * H.coeff b) (Finsupp.single a c) = _
  rw [Finsupp.linearCombination_single, smul_eq_mul]

theorem fischerPair_X_mul (H Q : Poly n) (i : Fin n) :
    fischerPair H (X i * Q) = fischerPair (pderiv i H) Q := by
  induction Q using MvPolynomial.induction_on' with
  | add A B hA hB => simp [mul_add, hA, hB]
  | monomial a c =>
    rw [X, monomial_mul_monomial, one_mul, add_comm, fischerPair_monomial,
      fischerPair_monomial, multiFactor_add_single, coeff_pderiv, Nat.cast_mul, Nat.cast_add_one]
    ring

/-- Multiplication by the squared radius is adjoint to the polynomial Laplacian. -/
theorem fischerPair_radiusSq_mul (H Q : Poly n) :
    fischerPair H (radiusSq n * Q) = fischerPair (lap H) Q := by
  simp only [radiusSq, Finset.sum_mul, map_sum, pow_two, mul_assoc, fischerPair_X_mul]
  simp only [fischerPair_sum, lap, coeff_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [Finset.mul_sum]

end Runcorn.Polynomial
