module

public import Runcorn.FischerPairing
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.Algebra.Order.Antidiag.Finsupp

/-!
# A polynomial representing the restriction of a functional to powers of linear forms

The coefficient computation in Lemma 3 of arXiv:2607.18379v1 identifies the
annihilator of the null powers. We use mathlib's multinomial coefficient
formula and its factorial identity to carry out the computation for an
arbitrary complex linear functional on polynomials.
-/

@[expose] public section
noncomputable section
open MvPolynomial
namespace Runcorn.Polynomial
variable {n : ℕ}

abbrev degreeIndices (n k : ℕ) : Finset (Fin n →₀ ℕ) :=
  Finset.finsuppAntidiag Finset.univ k

private theorem support_subset_indices {H : Poly n} {k : ℕ} (hH : H.IsHomogeneous k) :
    H.support ⊆ degreeIndices n k := by
  intro a ha
  apply Finset.mem_finsuppAntidiag.mpr
  exact ⟨(Finsupp.degree_eq_sum a).symm.trans (by rw [Finsupp.degree_eq_weight_one]; exact hH (mem_support_iff.mp ha)), Finset.subset_univ _⟩

private theorem apply_homogeneous (L : Poly n →ₗ[ℂ] ℂ) {H : Poly n} {k : ℕ}
    (hH : H.IsHomogeneous k) :
    L H = ∑ a ∈ degreeIndices n k, H.coeff a * L (monomial a 1) := by
  classical
  calc
    L H = ∑ a ∈ H.support, L (monomial a (H.coeff a)) := by
      rw [← map_sum, support_sum_monomial_coeff]
    _ = ∑ a ∈ H.support, H.coeff a * L (monomial a 1) := by
      apply Finset.sum_congr rfl
      intro a _
      have hm : monomial a (H.coeff a) = (H.coeff a) • (monomial a 1 : Poly n) := by
        simp [smul_monomial]
      rw [hm, map_smul, smul_eq_mul]
    _ = _ := Finset.sum_subset (support_subset_indices hH) fun a _ ha => by
      simp [notMem_support_iff.mp ha]

/-- The polynomial whose value at z is the functional applied to (z⋅X)^k. -/
def symbol (L : Poly n →ₗ[ℂ] ℂ) (k : ℕ) : Poly n :=
  ∑ a ∈ degreeIndices n k, monomial a ((a.multinomial : ℂ) * L (monomial a 1))

theorem coeff_symbol (L : Poly n →ₗ[ℂ] ℂ) (k : ℕ) (a : Fin n →₀ ℕ) :
    (symbol L k).coeff a =
      if a.degree = k then (a.multinomial : ℂ) * L (monomial a 1) else 0 := by
  classical
  simp [symbol, coeff_monomial, degreeIndices, Finsupp.degree_eq_sum]

/-- The evaluation identity follows from mathlib's finite-dimensional
multinomial expansion of a power of a linear combination of variables. -/
theorem eval_symbol (L : Poly n →ₗ[ℂ] ℂ) (k : ℕ) (z : Fin n → ℂ) :
    eval z (symbol L k) = L (linearForm z ^ k) := by
  classical
  rw [apply_homogeneous L (nullForm_homogeneous z k)]
  simp only [symbol, map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro a ha
  have hc := coeff_linearCombination_X_pow_of_fintype z a k
  rw [ite_eq_left (Finset.mem_finsuppAntidiag'.mp ha).1] at hc
  simp only [linearForm, ← smul_eq_C_mul, hc]
  ring

/-- The Fischer coefficient pairing of the dual symbol with a degree k
homogeneous polynomial recovers the functional, with the factor k!. -/
theorem factorial_mul_apply_eq (L : Poly n →ₗ[ℂ] ℂ) (k : ℕ) (H : Poly n)
    (hH : H.IsHomogeneous k) :
    (k.factorial : ℂ) * L H =
      ∑ a ∈ (symbol L k).support, (symbol L k).coeff a * ((multiFactor a : ℂ) * H.coeff a) := by
  classical
  have hs : (symbol L k).support ⊆ degreeIndices n k := by
    intro a ha
    by_contra h
    have : a.degree ≠ k := by simpa [degreeIndices, Finsupp.degree_eq_sum] using h
    exact (mem_support_iff.mp ha) (by simp [coeff_symbol, this])
  rw [Finset.sum_subset hs (fun a _ ha => by simp [notMem_support_iff.mp ha])]
  rw [apply_homogeneous L hH, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hd := (Finset.mem_finsuppAntidiag.mp ha).1
  have hmult : multiFactor a * a.multinomial = k.factorial := by
    rw [multiFactor, Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ a.support),
       Nat.multinomial_spec, hd]
  rw [coeff_symbol, ite_eq_left ((Finsupp.degree_eq_sum _).trans hd), ← hmult, Nat.cast_mul]
  ring

end Runcorn.Polynomial
