module

public import Runcorn.Definitions

/-! Independent statement checks of the Laurent exponent sets at low degrees. -/
@[expose] public section
namespace Review
open Runcorn

theorem planarLow : ∀ m : ℤ, ¬ momentExponent 2 0 m ∧ ¬ momentExponent 2 1 m := by
  intro m
  simp [momentExponent]

theorem planarDegreeTwo (m : ℤ) : momentExponent 2 2 m ↔ m = -2 := by
  simp only [momentExponent, ↓reduceIte, Nat.cast_ofNat]
  constructor
  · rintro ⟨l, hl, hm⟩
    omega
  · intro h
    exact ⟨0, by decide, by omega⟩

theorem spatialDegreeOne (m : ℤ) : momentExponent 3 1 m ↔ m = -2 := by
  simp only [momentExponent, ite_eq_right (by decide : (3 : ℕ) ≠ 2), Nat.cast_one, Nat.cast_ofNat]
  constructor
  · rintro ⟨l, hl, hm⟩
    omega
  · intro h
    exact ⟨0, by decide, by omega⟩

theorem spatialDegreeTwo (m : ℤ) : momentExponent 3 2 m ↔ m = -3 ∨ m = -1 := by
  simp only [momentExponent, ite_eq_right (by decide : (3 : ℕ) ≠ 2), Nat.cast_ofNat]
  constructor
  · rintro ⟨l, hl, hm⟩
    omega
  · rintro (h | h)
    · exact ⟨0, by decide, by omega⟩
    · exact ⟨1, by decide, by omega⟩

#print axioms planarLow
#print axioms planarDegreeTwo
#print axioms spatialDegreeOne
#print axioms spatialDegreeTwo
end Review
