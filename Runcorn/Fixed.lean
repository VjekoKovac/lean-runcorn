module

public import Runcorn.Definitions

/-!
# Polar integration and radial moments for Theorem 2

The polar-coordinate step uses the measure-preserving homeomorphism and surface
measure in mathlib's `MeasureTheory.Constructions.HaarToSphere`. The two index
changes follow the necessity and sufficiency arguments of Kovač and Smolić,
arXiv:2607.18379v1, Section 3.
-/

@[expose] public section

noncomputable section
open Set MeasureTheory Metric Filter
namespace Runcorn

/-- Polar integration with the angular integral taken first. The sphere measure is
mathlib's surface measure constructed from Lebesgue measure. The argument transports
the integrand through the measure-preserving polar homeomorphism and applies Fubini. -/
private theorem integral_polar {n : ℕ} (hn : 2 ≤ n)
    {F : Space n → ℂ} (hF : Integrable F) :
    (∫ x, F x) = ∫ r in Ioi (0 : ℝ), r ^ (n - 1) •
      (∫ σ : Sphere n, F (r • (σ : Space n)) ∂surfaceMeasure n) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let μ := (volume : Measure (Space n))
  let T := homeomorphUnitSphereProd (Space n)
  let G := fun y : Sphere n × Ioi (0 : ℝ) ↦ F ((T.symm y).val)
  have hp := μ.measurePreserving_homeomorphUnitSphereProd
  have hG : Integrable G (μ.toSphere.prod (.volumeIoiPow (Module.finrank ℝ (Space n) - 1))) := by
    apply (hp.integrable_comp_emb (Homeomorph.measurableEmbedding _)).mp
    simpa only [G, T, Function.comp_def, Homeomorph.symm_apply_apply] using
      (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : Space n)).compl).mp
        (hF.integrableOn (s := ({0}ᶜ : Set (Space n))))
  calc
    _ = ∫ x : ({0}ᶜ : Set (Space n)), F x.1 ∂μ.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫ y, G y ∂μ.toSphere.prod (.volumeIoiPow (Module.finrank ℝ (Space n) - 1)) := by
      simpa only [G, T, Homeomorph.symm_apply_apply] using hp.integral_comp (Homeomorph.measurableEmbedding _) G
    _ = ∫ r : Ioi (0 : ℝ), (∫ σ : Sphere n, F (r.1 • (σ : Space n)) ∂μ.toSphere)
        ∂.volumeIoiPow (n - 1) := by
      simpa [G, T] using integral_prod_symm G hG
    _ = _ := by
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul (measurable_subtype_coe.pow_const _).real_toNNReal,
        integral_subtype_comap measurableSet_Ioi (fun r : ℝ ↦
          Real.toNNReal (r ^ (n - 1)) • ∫ σ : Sphere n, F (r • (σ : Space n)) ∂μ.toSphere)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.out.le _)]
      rfl

/-- The spherical-coordinate formula on the paper's closed annulus. Only the restriction
of the integrand to the annulus needs to be integrable. -/
theorem integral_annulus_polar {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} (ha : 0 < a)
    {F : Space n → ℂ} (hF : IntegrableOn F (annulus a b)) :
    (∫ x in annulus a b, F x) = ∫ r in Icc a b, r ^ (n - 1) •
      (∫ σ : Sphere n, F (r • (σ : Space n)) ∂surfaceMeasure n) := by
  classical
  have hA : MeasurableSet (annulus (n := n) a b) :=
    (measurableSet_Icc.preimage continuous_norm.measurable)
  rw [← integral_indicator hA, integral_polar hn ((integrable_indicator_iff hA).mpr hF)]
  let J := fun r : ℝ ↦ r ^ (n - 1) •
    (∫ σ : Sphere n, F (r • (σ : Space n)) ∂surfaceMeasure n)
  calc
    _ = ∫ r in Ioi (0 : ℝ), (Icc a b).indicator J r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hrad (σ : Sphere n) : ‖r • (σ : Space n)‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp σ.2, mul_one]
      by_cases hab : r ∈ Icc a b
      · simp only [indicator_of_mem hab, J]
        have hσ (σ : Sphere n) : r • (σ : Space n) ∈ annulus a b := by
          simpa [annulus, hrad] using hab
        simp [hσ]
      · have hσ (σ : Sphere n) : r • (σ : Space n) ∉ annulus a b := by
          simpa [annulus, hrad] using hab
        simp [hσ, hab]
    _ = _ := by
      rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
        inter_eq_left.mpr (show Icc a b ⊆ Ioi 0 from fun r hr ↦ ha.trans_le hr.1)]

/-- The change of index `q = k - 1 - ℓ` used in the necessity proof. Natural
subtraction occurs only in witness construction; the displayed powers use integers. -/
theorem momentExponent_iff_kelvinIndex {n k : ℕ} (hn : 2 ≤ n) (m : ℤ) :
    momentExponent n k m ↔
      ∃ q : ℕ, q < k ∧ (n = 2 → 1 ≤ q) ∧ m = (k : ℤ) - (n : ℤ) - 2 * q := by
  by_cases h : n = 2
  · subst n
    simp only [momentExponent, ite_true, true_implies]
    constructor
    · rintro ⟨l, hl, hm⟩
      exact ⟨k - 1 - l, by omega, by omega, by omega⟩
    · rintro ⟨q, hq, hq', hm⟩
      exact ⟨k - 1 - q, by omega, by omega⟩
  · simp only [momentExponent, h, false_implies, true_and]
    constructor
    · rintro ⟨l, hl, hm⟩
      exact ⟨k - 1 - l, by omega, by omega⟩
    · rintro ⟨q, hq, hm⟩
      exact ⟨k - 1 - q, by omega, by omega⟩

/-- Every surviving term of the gradient-product decomposition has exactly one
of the allowed radial powers, including the exceptional upper cutoff in dimension two. -/
theorem momentExponent_of_gradient_indices {n p q l : ℕ} (hn : 2 ≤ n)
    (hp : l < p) (hq : l ≤ q) (hq₂ : n = 2 → l < q) :
    momentExponent n (p + q - 2 * l) ((p : ℤ) - (q : ℤ) - (n : ℤ)) := by
  apply (momentExponent_iff_kelvinIndex hn _).mpr
  exact ⟨q - l, by omega, by intro h; specialize hq₂ h; omega, by omega⟩

/-- Every claimed power is realized already by the special pair with degree
sum `p + q = k`, where the exterior degree is positive in the plane. -/
theorem momentExponent_iff_special_pair {n k : ℕ} (hn : 2 ≤ n) (m : ℤ) :
    momentExponent n k m ↔ ∃ p q : ℕ, 0 < p ∧ (n = 2 → 0 < q) ∧
      p + q = k ∧ m = (p : ℤ) - (q : ℤ) - (n : ℤ) := by
  rw [momentExponent_iff_kelvinIndex hn]
  constructor
  · rintro ⟨q, hq, hq₂, hm⟩
    exact ⟨k - q, q, by omega, hq₂, by omega, by omega⟩
  · rintro ⟨p, q, hp, hq₂, hk, hm⟩
    exact ⟨q, by omega, hq₂, by omega⟩

/-- With the radial weight included the Laurent exponent loses all dependence
on dimension. This gives the unweighted moment in the necessity argument. -/
theorem weighted_kelvin_power {n k q : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 < r) :
    r ^ ((k : ℤ) - (n : ℤ) - 2 * q) * r ^ (n - 1) =
      r ^ ((k : ℤ) - 1 - 2 * q) := by
  rw [← zpow_natCast, ← zpow_add₀ hr.ne']
  congr 1
  omega

/-- Integration against the paper's radial measure in ordinary Lebesgue coordinates. -/
theorem integral_radialMeasure (n : ℕ) {a b : ℝ} (ha : 0 < a) (h : ℝ → ℂ) :
    (∫ r, h r ∂radialMeasure n a b) = ∫ r in Icc a b, r ^ (n - 1) • h r := by
  simp only [radialMeasure, ENNReal.ofReal]
  have hmeas : Measurable (fun r : ℝ ↦ Real.toNNReal (r ^ (n - 1))) :=
    (measurable_id.pow_const _).real_toNNReal
  rw [integral_withDensity_eq_integral_smul hmeas]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  dsimp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (ha.le.trans hr.1) _)]

/-- Evaluation of a spherical harmonic, or any spherical function, along a positive ray. -/
theorem atDirection_pos_smul {n : ℕ} (Y : Sphere n → ℂ) {r : ℝ} (hr : 0 < r)
    (σ : Sphere n) : atDirection Y (r • (σ : Space n)) = Y σ := by
  have hd : ‖r • (σ : Space n)‖⁻¹ • (r • (σ : Space n)) = σ.val := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mem_sphere_zero_iff_norm.mp σ.2,
      mul_one, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  simp [atDirection, hd]

/-- The unnormalized coefficient from (1.4), evaluated with an arbitrary angular
test. Choosing the conjugate basis element gives the numerator of that coefficient. -/
def angularIntegral {n : ℕ} (f : Space n → ℂ) (Y : Sphere n → ℂ) (r : ℝ) : ℂ :=
  ∫ σ : Sphere n, f (r • (σ : Space n)) * Y σ ∂surfaceMeasure n

/-- The polar-coordinate step in both directions of Theorem 2. A single separated
test on the annulus gives precisely the corresponding radial moment of the
angular integral, for every integer exponent. -/
theorem annular_pairing_eq_radial_moment {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} (ha : 0 < a)
    (f : Space n → ℂ) (Y : Sphere n → ℂ) (m : ℤ)
    (hF : IntegrableOn (fun x : Space n ↦
      f x * atDirection Y x * ((‖x‖ ^ m : ℝ) : ℂ)) (annulus a b)) :
    (∫ x in annulus a b, f x * atDirection Y x * ((‖x‖ ^ m : ℝ) : ℂ)) =
      ∫ r, angularIntegral f Y r * ((r ^ m : ℝ) : ℂ) ∂radialMeasure n a b := by
  rw [integral_annulus_polar hn ha hF, integral_radialMeasure n ha]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  have hrpos : 0 < r := ha.trans_le hr.1
  have hrad (σ : Sphere n) : ‖r • (σ : Space n)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, mem_sphere_zero_iff_norm.mp σ.2, mul_one]
  simp only [atDirection_pos_smul _ hrpos, hrad, angularIntegral]
  rw [integral_mul_const]

/-- Normalizing the angular coefficient by a nonzero scalar preserves, in both
directions, the vanishing of the radial moment. Orthogonal bases need not have unit norm. -/
theorem normalized_radial_moment_eq_zero_iff {n : ℕ} (a b : ℝ) (g : ℝ → ℂ) (m : ℤ)
    {c : ℂ} (hc : c ≠ 0) :
    (∫ r, (g r / c) * ((r ^ m : ℝ) : ℂ) ∂radialMeasure n a b) = 0 ↔
      (∫ r, g r * ((r ^ m : ℝ) : ℂ) ∂radialMeasure n a b) = 0 := by
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div, div_eq_zero_iff]
  simp [hc]

end Runcorn
