module

public import Runcorn.Symbol
public import Runcorn.Quadric
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The null-power spanning lemma

We follow the duality argument of Kovač and Smolić, Section 2, Lemma 3.
Any algebraic linear functional annihilating the null powers corresponds to a
polynomial vanishing on the null quadric. Divisibility by the squared radius
and the Fischer adjoint identity imply that the functional vanishes on all
homogeneous harmonic polynomials of the prescribed degree.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace Runcorn.Polynomial
variable {n : ℕ}

def nullPowers (n k : ℕ) : Set (Poly n) :=
  {P | ∃ z : Fin n → ℂ, ∑ i, z i ^ 2 = 0 ∧ P = linearForm z ^ k}

/-- A homogeneous harmonic polynomial is a finite linear combination of powers
of null linear forms. -/
theorem mem_span_nullPowers (hn : 2 ≤ n) (k : ℕ) (H : Poly n) (hh : H.IsHomogeneous k)
    (hH : lap H = 0) : H ∈ Submodule.span ℂ (nullPowers n k) := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ _).mp
  intro L hL
  have hz (z : Fin n → ℂ) (hnull : ∑ i, z i ^ 2 = 0) :
      eval z (symbol L k) = 0 := by
    rw [eval_symbol]
    exact ((Submodule.mem_dualAnnihilator L).mp hL) _
      (Submodule.subset_span (show linearForm z ^ k ∈ nullPowers n k from ⟨z, hnull, rfl⟩))
  obtain ⟨Q, hQ⟩ := radiusSq_dvd_of_vanishes_on_null_cone hn (symbol L k) hz
  have hp : fischerPair H (symbol L k) = 0 := by
    rw [hQ, fischerPair_radiusSq_mul, hH, fischerPair_sum]
    simp
  rw [fischerPair_sum] at hp
  have h := factorial_mul_apply_eq L k H hh
  rw [← h] at hp
  exact (mul_eq_zero.mp hp).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))

/-- Exact span equality for the solid spherical harmonics (Lemma 3). -/
theorem span_nullPowers_iff (hn : 2 ≤ n) (k : ℕ) (H : Poly n) :
    H ∈ Submodule.span ℂ (nullPowers n k) ↔ H.IsHomogeneous k ∧ lap H = 0 := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨z,hz,rfl⟩ := hP
      exact ⟨nullForm_homogeneous z k, lap_nullForm_pow z hz k⟩
    | zero =>
      exact ⟨isHomogeneous_zero _ _ k, by simp [lap]⟩
    | add P Q _ _ hP hQ =>
      exact ⟨hP.1.add hQ.1, by rw [lap_add, hP.2, hQ.2, add_zero]⟩
    | smul c P _ hP =>
      rw [← C_mul']
      exact ⟨hP.1.C_mul c, by rw [lap_const_mul, hP.2, mul_zero]⟩
  · rintro ⟨hh,hH⟩
    exact mem_span_nullPowers hn k H hh hH

end Runcorn.Polynomial
