module

public import Runcorn.AngularSpan
public import Runcorn.Decay
public import Runcorn.Kelvin

/-!
# Necessary radial moment conditions for the fixed-annulus theorem

Combining null-power spanning with the admissible special pairs removes the
algebraic and potential-theoretic hypotheses of the intermediate deduction.
The coefficient is defined directly by the original sphere integral.
-/

@[expose] public section
noncomputable section
open MeasureTheory InnerProductSpace Set
open scoped ComplexConjugate

namespace Runcorn

theorem specialPair_admissible {n p q : ℕ} (hn : 2 ≤ n) (hq : n = 2 → 0 < q)
    {lo hi : ℝ} (hlo : 0 < lo) (ζ : Fin n → ℂ) (hz : ∑ i, ζ i ^ 2 = 0) :
    Admissible lo hi (fun x ↦ SpecialPair.form ζ x ^ p)
      (fun x ↦ ((‖x‖ ^ (2 - (n : ℤ) - 2*q) : ℝ) : ℂ) * SpecialPair.form ζ x ^ q) := by
  refine ⟨?_, ?_, specialPair_vanishes_at_infinity hn hq ζ⟩
  · rw [← polynomialValue_linearForm_pow]
    exact (harmonic_polynomialValue _ (Polynomial.lap_nullForm_pow ζ hz p)).mono (subset_univ _)
  · have h := kelvin_harmonicOn _ (Polynomial.nullForm_homogeneous ζ q)
      (Polynomial.lap_nullForm_pow ζ hz q)
    have he : weightedPoly (2-(n:ℤ)-2*q) (Polynomial.linearForm ζ ^ q) =
        (fun x ↦ ((‖x‖ ^ (2-(n:ℤ)-2*q) : ℝ) : ℂ) * SpecialPair.form ζ x ^ q) := by
      funext x
      rw [weightedPoly, polynomialValue_linearForm_pow]
    rw [he] at h
    exact h.mono fun x hx ↦ norm_pos_iff.mp (hlo.trans hx)

/-- Every solution of the fixed-annulus tests has all the prescribed vanishing
moments for its normalized spherical coefficients, for every orthogonal basis,
in all dimensions. The L² expansion itself is a separate assertion. -/
theorem fixedTests_normalized_moments {n : ℕ} (hn : 2 ≤ n) {lo hi a b : ℝ}
    (hlo : 0 < lo) (ha : lo < a)
    {f : Space n → ℂ} (hf : MemLp f 2 (volume.restrict (annulus a b)))
    (ht : FixedTests lo hi a b f) (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (k : ℕ) (j : Fin (harmonicDimension n k)) (m : ℤ) (hm : momentExponent n k m) :
    (∫ r, (angularIntegral f (fun σ ↦ conj (Y k j σ)) r /
      (∫ σ : Sphere n, Y k j σ * conj (Y k j σ) ∂surfaceMeasure n)) *
        ((r ^ m : ℝ) : ℂ) ∂radialMeasure n a b) = 0 := by
  apply normalized_moments_of_special_tests hn (hlo.trans ha) hf ht Y hY k j
    (sphericalHarmonic_mem_nullPower_span hn ((hY k).1 j).conj) _ m hm
  intro p q _ hq _ ζ hz
  exact specialPair_admissible hn hq hlo ζ hz

end Runcorn
