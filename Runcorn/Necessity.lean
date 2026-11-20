module

public import Runcorn.Separated
public import Runcorn.SpecialPair

/-!
# Necessity of the radial moments

The polar pairing, linearity on the null-power span, and the normalization
are the steps following equation (3.1) of Kovač and Smolić. The theorem with
explicit spanning and admissibility hypotheses isolates the two algebraic
and potential-theoretic ingredients used in this deduction.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ComplexConjugate

namespace Runcorn

/-- Restriction of the degree-k power of a complex linear form to the sphere. -/
def angularPower {n : ℕ} (ζ : Fin n → ℂ) (k : ℕ) (σ : Sphere n) : ℂ :=
  SpecialPair.form ζ (σ : Space n) ^ k

def nullPowerSet (n k : ℕ) : Set (Sphere n → ℂ) :=
  {Y | ∃ ζ : Fin n → ℂ, (∑ i, ζ i ^ 2) = 0 ∧ Y = angularPower ζ k}

theorem angularPower_continuous {n : ℕ} (ζ : Fin n → ℂ) (k : ℕ) :
    Continuous (angularPower ζ k) :=
  ((SpecialPair.form ζ).continuous.comp continuous_subtype_val).pow _

theorem form_pow_radial {n : ℕ} (ζ : Fin n → ℂ) (k : ℕ) {x : Space n} (hx : x ≠ 0) :
    SpecialPair.form ζ x ^ k =
      ((‖x‖ ^ k : ℝ) : ℂ) * atDirection (angularPower ζ k) x := by
  have hr := norm_pos_iff.mpr hx
  have hσ : ‖x‖⁻¹ • x ∈ sphere (0 : Space n) 1 := by
    simp [norm_smul, hr.ne']
  simp only [atDirection, dite_eq_left hσ, angularPower, map_smul, Complex.real_smul,
    Complex.ofReal_pow, Complex.ofReal_inv, mul_pow, inv_pow]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')), one_mul]

/-- Each admissible pair from Lemma 4 forces one separated annular test, with
the exact angular power and radial exponent from the necessity proof. -/
theorem special_pair_test_zero {n p q : ℕ} (hn : 2 ≤ n) (hp : 0 < p) (hq : n = 2 → 0 < q)
    {lo hi a b : ℝ} (ha : 0 < a) {f : Space n → ℂ} (ht : FixedTests lo hi a b f)
    (ζ : Fin n → ℂ) (hz : ∑ i, ζ i ^ 2 = 0)
    (huv : Admissible lo hi (fun x ↦ SpecialPair.form ζ x ^ p)
      (fun x ↦ ((‖x‖ ^ (2 - (n : ℤ) - 2*q) : ℝ) : ℂ) * SpecialPair.form ζ x ^ q)) :
    (∫ x in annulus a b, f x * atDirection (angularPower ζ (p + q)) x *
      ((‖x‖ ^ ((p : ℤ) - q - n) : ℝ) : ℂ)) = 0 := by
  let s : ℤ := 2 - (n : ℤ) - 2*q
  let c : ℂ := p * (s : ℂ)
  have hs : s ≠ 0 := by dsimp [s]; by_cases hn₂ : n = 2 <;> omega
  have hc : c ≠ 0 := mul_ne_zero (by exact_mod_cast hp.ne') (by exact_mod_cast hs)
  have h := ht _ _ huv
  have hA := (isCompact_annulus (n := n) a b).measurableSet
  apply ((mul_eq_zero (a := c)).mp ?_).resolve_left hc
  rw [← integral_const_mul]
  refine Eq.trans (setIntegral_congr_fun hA ?_) h
  intro x hx
  have h0 : x ≠ 0 := norm_pos_iff.mp (ha.trans_le hx.1)
  have hgrad := SpecialPair.gradient_product ζ hz p q hp s h0
  change c * (f x * atDirection (angularPower ζ (p+q)) x * _) =
    f x * gradDot _ _ x
  rw [gradDot, hgrad, form_pow_radial ζ (p+q) h0]
  have he : ((‖x‖ ^ ((p : ℤ) - q - n) : ℝ) : ℂ) =
      (‖x‖ ^ (s-2) : ℝ) * ((‖x‖ ^ (p+q) : ℝ) : ℂ) := by
    have hrpow : ‖x‖ ^ ((p : ℤ) - q - n) = ‖x‖ ^ (s-2) * ‖x‖ ^ (p+q) := by
      rw [← zpow_natCast, ← zpow_add₀ (norm_ne_zero_iff.mpr h0)]
      congr 1
      dsimp only [s]
      omega
    exact_mod_cast hrpow
  rw [he]
  dsimp [c]
  ring

private theorem atDirection_add_apply {n : ℕ} (Y Z : Sphere n → ℂ) (x : Space n) :
    atDirection (Y + Z) x = atDirection Y x + atDirection Z x := by
  by_cases hx : ‖‖x‖⁻¹ • x‖ = 1 <;> simp [atDirection, hx]

private theorem atDirection_smul_apply {n : ℕ} (c : ℂ) (Y : Sphere n → ℂ) (x : Space n) :
    atDirection (c • Y) x = c * atDirection Y x := by
  by_cases hx : ‖‖x‖⁻¹ • x‖ = 1 <;> simp [atDirection, hx]

/-- A continuous angular test in the algebraic span of the special tests inherits
vanishing by linearity. The L² hypothesis gives absolute integrability before
the integral of the sum is split. -/
theorem annular_test_zero_on_span {n k : ℕ} {a b : ℝ} (ha : 0 < a)
    {f : Space n → ℂ} (hf : MemLp f 2 (volume.restrict (annulus a b))) (m : ℤ)
    (hnull : ∀ ζ : Fin n → ℂ, (∑ i, ζ i ^ 2) = 0 →
      (∫ x in annulus a b, f x * atDirection (angularPower ζ k) x * ((‖x‖ ^ m : ℝ) : ℂ)) = 0)
    {Y : Sphere n → ℂ} (hY : Y ∈ Submodule.span ℂ (nullPowerSet n k)) :
    (∫ x in annulus a b, f x * atDirection Y x * ((‖x‖ ^ m : ℝ) : ℂ)) = 0 := by
  suffices h : Continuous Y ∧
      (∫ x in annulus a b, f x * atDirection Y x * ((‖x‖ ^ m : ℝ) : ℂ)) = 0 from h.2
  induction hY using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ζ, hz, rfl⟩ := hy
    exact ⟨angularPower_continuous ζ k, hnull ζ hz⟩
  | zero =>
    refine ⟨continuous_const, ?_⟩
    have hzero (x : Space n) : atDirection (0 : Sphere n → ℂ) x = 0 := by
      by_cases hx : ‖‖x‖⁻¹ • x‖ = 1 <;> simp [atDirection, hx]
    simp [hzero]
  | add y z _ _ hy hz =>
    refine ⟨hy.1.add hz.1, ?_⟩
    simp_rw [atDirection_add_apply, mul_add, add_mul]
    rw [integral_add (integrableOn_separatedTest ha hf hy.1 m)
      (integrableOn_separatedTest ha hf hz.1 m), hy.2, hz.2, zero_add]
  | smul c y _ hy =>
    refine ⟨continuous_const.smul hy.1, ?_⟩
    simp_rw [atDirection_smul_apply, mul_left_comm (f _) c, mul_assoc c]
    rw [integral_const_mul, hy.2, mul_zero]

/-- The conclusion of the necessity argument about every normalized basis moment,
given the null-power spanning membership (Lemma 3) and admissibility (Lemma 4).
No spherical expansion or coefficient-vanishing assumption is an input. -/
theorem normalized_moments_of_special_tests {n : ℕ} (hn : 2 ≤ n) {lo hi a b : ℝ}
    (ha : 0 < a) {f : Space n → ℂ} (hf : MemLp f 2 (volume.restrict (annulus a b)))
    (ht : FixedTests lo hi a b f) (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (k : ℕ) (j : Fin (harmonicDimension n k))
    (hspan : (fun σ ↦ conj (Y k j σ)) ∈ Submodule.span ℂ (nullPowerSet n k))
    (hadm : ∀ p q : ℕ, 0 < p → (n = 2 → 0 < q) → p+q = k →
      ∀ ζ : Fin n → ℂ, (∑ i, ζ i ^ 2) = 0 →
      Admissible lo hi (fun x ↦ SpecialPair.form ζ x ^ p)
        (fun x ↦ ((‖x‖ ^ (2 - (n : ℤ) - 2*q) : ℝ) : ℂ) * SpecialPair.form ζ x ^ q)) :
    ∀ m : ℤ, momentExponent n k m →
      (∫ r, (angularIntegral f (fun σ ↦ conj (Y k j σ)) r /
        (∫ σ : Sphere n, Y k j σ * conj (Y k j σ) ∂surfaceMeasure n)) *
          ((r ^ m : ℝ) : ℂ) ∂radialMeasure n a b) = 0 := by
  apply (separatedTests_iff_normalized_moments hn ha hf
    (Complex.continuous_conj.comp ((hY k).1 j).continuous) (angularMass_ne_zero Y hY k j)).mp
  intro m hm
  obtain ⟨p, q, hp, hq, rfl, rfl⟩ := (momentExponent_iff_special_pair hn m).mp hm
  apply annular_test_zero_on_span ha hf _ _ hspan
  intro ζ hz
  exact special_pair_test_zero hn hp hq ha ht ζ hz (hadm p q hp hq rfl ζ hz)

end Runcorn
