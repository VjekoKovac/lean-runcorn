module

public import Runcorn.Restriction
public import Runcorn.NullSpan

/-! # The null powers span each degree on the real unit sphere -/

@[expose] public section
noncomputable section
open Set MvPolynomial InnerProductSpace
open scoped ComplexConjugate

namespace Runcorn

/-- Conjugating the coefficients of a polynomial conjugates its values on real points. -/
theorem polynomialValue_conj {n : ℕ} (P : Polynomial.Poly n) :
    polynomialValue (MvPolynomial.map (starRingEnd ℂ) P) =
      Complex.conjCLE ∘ polynomialValue P := by
  funext x
  have h := MvPolynomial.map_eval (starRingEnd ℂ) (fun i ↦ (x i : ℂ)) P
  simpa [polynomialValue, Function.comp_def] using h.symm

theorem IsSphericalHarmonic.conj {n k : ℕ} {Y : Sphere n → ℂ} (h : IsSphericalHarmonic k Y) :
    IsSphericalHarmonic k (fun σ ↦ conj (Y σ)) := by
  obtain ⟨P, hd, hh, hY⟩ := h
  refine ⟨MvPolynomial.map (starRingEnd ℂ) P, hd.map _, ?_, ?_⟩
  · rw [polynomialValue_conj]
    exact hh.comp_CLM Complex.conjCLE.toContinuousLinearMap
  · intro σ
    simp [polynomialValue_conj, hY σ]

theorem sphericalHarmonic_mem_nullPower_span {n k : ℕ} (hn : 2 ≤ n)
    {Y : Sphere n → ℂ} (hY : IsSphericalHarmonic k Y) :
    Y ∈ Submodule.span ℂ (nullPowerSet n k) := by
  obtain ⟨P, hd, hh, hY⟩ := hY
  rw [funext hY]
  have hspan := Polynomial.mem_span_nullPowers hn k P hd (polynomial_lap_eq_zero_of_harmonic P hh)
  clear hd hh hY
  induction hspan using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨ζ, hz, rfl⟩ := hQ
    exact Submodule.subset_span ⟨ζ, hz, by rw [polynomialValue_linearForm_pow]; rfl⟩
  | zero =>
    convert (Submodule.zero_mem (Submodule.span ℂ (nullPowerSet n k)))
    simp [polynomialValue]
  | add Q R _ _ hQ hR =>
    simpa [polynomialValue, map_add, Pi.add_def] using Submodule.add_mem _ hQ hR
  | smul c Q _ hQ =>
    simpa [polynomialValue, ← MvPolynomial.C_mul', Pi.smul_def, smul_eq_mul] using
      Submodule.smul_mem (Submodule.span ℂ (nullPowerSet n k)) c hQ

end Runcorn
