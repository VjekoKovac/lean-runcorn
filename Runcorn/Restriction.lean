module

public import Runcorn.Necessity
public import Runcorn.PolynomialCalculus
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Restriction of complex polynomials to real Euclidean space

A complex polynomial vanishing at every real point vanishes identically. This
converts the analytic harmonicity in the definition of a spherical harmonic
back into the formal polynomial Laplacian needed by the Fischer argument.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Metric MvPolynomial InnerProductSpace Laplacian
open scoped ComplexConjugate

namespace Runcorn

theorem polynomialValue_injective {n : ℕ} :
    Function.Injective (polynomialValue (n := n)) := by
  intro P Q h
  apply MvPolynomial.funext_set (fun _ : Fin n ↦ Set.range Complex.ofReal)
    (fun _ ↦ Set.infinite_range_of_injective Complex.ofReal_injective)
  intro z hz
  choose r hr using fun i : Fin n ↦ hz i (Set.mem_univ i)
  have he := congrFun h (WithLp.toLp 2 r)
  simpa only [polynomialValue, PiLp.toLp_apply, funext hr] using he

theorem polynomial_lap_eq_zero_of_harmonic {n : ℕ} (P : Polynomial.Poly n)
    (hP : HarmonicOnNhd (polynomialValue P) univ) : Polynomial.lap P = 0 := by
  apply polynomialValue_injective
  funext x
  rw [← laplacian_polynomialValue]
  simpa [polynomialValue] using (hP x (mem_univ _)).2.self_of_nhds

theorem polynomialValue_linearForm_pow {n : ℕ} (ζ : Fin n → ℂ) (k : ℕ) :
    polynomialValue (Polynomial.linearForm ζ ^ k) = (fun x ↦ SpecialPair.form ζ x ^ k) := by
  funext x
  simp [polynomialValue, Polynomial.linearForm, SpecialPair.form_apply, map_sum]

theorem angularPower_conj {n : ℕ} (ζ : Fin n → ℂ) (k : ℕ) :
    (fun σ ↦ conj (angularPower ζ k σ)) = angularPower (fun i ↦ conj (ζ i)) k := by
  funext σ
  simp [angularPower, SpecialPair.form_apply, map_sum]

end Runcorn
