module

public import Runcorn.Algebra
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Nullstellensatz

/-!
# Divisibility on the null quadric

The proof of Lemma 3 in arXiv:2607.18379v1 divides by a monic polynomial in
the last variable. Here the same divisibility follows from mathlib's
`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` after establishing
squarefreeness using coordinate derivatives and the primeness of two distinct
coordinate variables. This use of the Nullstellensatz is the only change in
this step of the argument.
-/

@[expose] public section
noncomputable section
open MvPolynomial
namespace Runcorn.Polynomial
variable {n : ℕ}

/-- The complex quadratic form defining the null cone is squarefree, also in
dimension two, where it factors into two distinct linear terms. -/
theorem radiusSq_squarefree (hn : 2 ≤ n) : Squarefree (radiusSq n) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)
  apply (squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible
    ⟨X i, (X_prime (R := ℂ) (i := i)).irreducible⟩).mpr
  intro q hq hd
  obtain ⟨A, hA⟩ := hd
  have divides (t : Fin n) : q ∣ X t := by
    have hd' : q ∣ 2 * X t := by
      rw [← pderiv_radiusSq, hA, pderiv_mul, pderiv_mul]
      exact ⟨(2 * pderiv t q) * A + q * pderiv t A, by ring⟩
    have hu : IsUnit (2 : Poly n) := by
      have hc := ((isUnit_iff_ne_zero.mpr (by norm_num : (2:ℂ) ≠ 0)).map
        (MvPolynomial.C : ℂ →+* Poly n))
      rw [map_ofNat] at hc
      exact hc
    exact (hq.prime.dvd_mul.mp hd').resolve_left fun h => hq.not_isUnit (isUnit_of_dvd_unit h hu)
  have hqi := hq.associated_of_dvd (X_prime (R := ℂ) (i := i)).irreducible (divides i)
  exact hij (X_dvd_X.mp (hqi.symm.dvd.trans (divides j)))

/-- The divisibility step of Lemma 3 of arXiv:2607.18379v1. This proof
uses mathlib's Hilbert Nullstellensatz for the radical of a principal ideal. -/
theorem radiusSq_dvd_of_vanishes_on_null_cone (hn : 2 ≤ n) (P : Poly n)
    (hP : ∀ z : Fin n → ℂ, (∑ i, z i ^ 2) = 0 → eval z P = 0) :
    radiusSq n ∣ P := by
  let J : Ideal (Poly n) := Ideal.span {radiusSq n}
  have hm : P ∈ vanishingIdeal ℂ (zeroLocus ℂ J) := by
    intro z hz
    have hR := hz (radiusSq n) (Ideal.subset_span (by simp))
    rw [aeval_eq_eval] at hR ⊢
    apply hP z
    simpa [radiusSq] using hR
  rw [vanishingIdeal_zeroLocus_eq_radical] at hm
  obtain ⟨s, hs⟩ := Ideal.mem_radical_iff.mp hm
  exact (radiusSq_squarefree hn).isRadical s P (Ideal.mem_span_singleton.mp hs)
end Runcorn.Polynomial
