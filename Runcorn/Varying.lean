module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Runcorn.Definitions
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The one-dimensional differentiation and angular continuity arguments of Theorem 1.
The FTC and continuity of parametric integration are reused from mathlib. -/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
noncomputable section
namespace Runcorn

/-- A continuous complex density vanishes at every interior point exactly when all
its integrals with strictly ordered interior endpoints vanish. -/
theorem intervalIntegral_zero_iff {lo hi : ℝ} {F : ℝ → ℂ}
    (hc : ContinuousOn F (Ioo lo hi)) :
    (∀ a b : ℝ, lo < a → a < b → b < hi → (∫ t in a..b, F t) = 0) ↔
      ∀ r ∈ Ioo lo hi, F r = 0 := by
  constructor
  · intro hz r hr
    obtain ⟨a, hla, har⟩ := exists_between hr.1
    have hsub : uIcc a r ⊆ Ioo lo hi := by
      rw [uIcc_of_le har.le]
      intro t ht
      exact ⟨hla.trans_le ht.1, ht.2.trans_lt hr.2⟩
    have hder := intervalIntegral.integral_hasDerivAt_right
      ((hc.mono hsub).intervalIntegrable)
      (hc.stronglyMeasurableAtFilter isOpen_Ioo r hr)
      (hc.continuousAt (isOpen_Ioo.mem_nhds hr))
    have heq : (fun t ↦ ∫ s in a..t, F s) =ᶠ[𝓝 r] fun _ ↦ (0 : ℂ) := by
      filter_upwards [Ioo_mem_nhds har hr.2] with t ht
      exact hz a t hla ht.1 ht.2
    exact (hder.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const r (0 : ℂ))
  · intro hz a b hla hab hbh
    rw [← intervalIntegral.integral_zero (a := a) (b := b) (E := ℂ)]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab.le]
    intro t ht
    exact hz t ⟨hla.trans_le ht.1, ht.2.trans_lt hbh⟩

/-- A nonzero Laurent weight cannot hide a continuous coefficient on a
positive interval, even for negative exponents. -/
theorem coefficient_zero_of_all_laurent_moments {lo hi : ℝ} (hlo : 0 ≤ lo)
    {g : ℝ → ℂ} (hc : ContinuousOn g (Ioo lo hi)) (m : ℤ)
    (hz : ∀ a b : ℝ, lo < a → a < b → b < hi →
      (∫ t in a..b, g t * (t : ℂ) ^ m) = 0) :
    ∀ r ∈ Ioo lo hi, g r = 0 := by
  have hnonzero (r : ℝ) (hr : r ∈ Ioo lo hi) : (r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hlo.trans_lt hr.1).ne'
  have hpow : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ m) (Ioo lo hi) :=
    Complex.continuous_ofReal.continuousOn.zpow₀ m (fun r hr ↦ Or.inl (hnonzero r hr))
  intro r hr
  have hval := (intervalIntegral_zero_iff (hc.mul hpow)).mp hz r hr
  exact (mul_eq_zero.mp hval).resolve_right (zpow_ne_zero m (hnonzero r hr))


/-- The weighted measure used in Theorem 2 becomes the ordinary interval
integral after adding the Jacobian exponent to the Laurent exponent. -/
theorem radial_moment_eq_intervalIntegral (n : ℕ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (g : ℝ → ℂ) (m : ℤ) :
    (∫ t, g t * ((t ^ m : ℝ) : ℂ) ∂radialMeasure n a b) =
      ∫ t in a..b, g t * (t : ℂ) ^ (m + ((n - 1 : ℕ) : ℤ)) := by
  unfold radialMeasure
  have hm : Measurable (fun r : ℝ ↦ ENNReal.ofReal (r ^ (n-1))) := by fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  have ht0 : 0 < t := ha.trans_le ht.1
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  simp [ENNReal.toReal_ofReal (pow_nonneg ht0.le _), Complex.real_smul,
    zpow_add₀ htC, mul_comm, mul_assoc]

/-- A radius-dependent coefficient in every fixed-annulus moment space is zero
whenever the degree has a moment condition. This formalizes the elimination
of the positive degrees, except for degree one in the plane. -/
theorem coefficient_zero_of_all_moment_spaces {n k : ℕ} {lo hi : ℝ} (hlo : 0 ≤ lo)
    {g : ℝ → ℂ} (hc : ContinuousOn g (Ioo lo hi))
    (hex : ∃ m : ℤ, momentExponent n k m)
    (hmem : ∀ a b : ℝ, lo < a → a < b → b < hi → InMomentSpace n k a b g) :
    ∀ r ∈ Ioo lo hi, g r = 0 := by
  obtain ⟨m, hm⟩ := hex
  apply coefficient_zero_of_all_laurent_moments hlo hc (m + ((n-1 : ℕ) : ℤ))
  intro a b hla hab hbh
  rw [← radial_moment_eq_intervalIntegral n (hlo.trans_lt hla) hab.le g m]
  exact (hmem a b hla hab hbh).2 m hm

/-- The end exponents selected in the proof of Theorem 1, with integer
subtraction (in particular the planar k=2 term produces a negative power). -/
theorem terminal_moment_in_plane {k : ℕ} (hk : 2 ≤ k) :
    momentExponent 2 k ((k : ℤ) - 4) := by
  unfold momentExponent
  simp only [↓reduceIte]
  refine ⟨k-2, by omega, ?_⟩
  omega

theorem terminal_moment_in_higher_dimension {n k : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k) :
    momentExponent n k ((k : ℤ) - n) := by
  unfold momentExponent
  simp only [show n ≠ 2 by omega, ↓reduceIte]
  exact ⟨k-1, by omega, by omega⟩

/-- Integrating a continuous angular test against the spherical slices gives a
continuous function of the radius. This applies to every coefficient formula. -/
theorem continuousOn_angular_integral {n : ℕ} {lo hi : ℝ} (hlo : 0 ≤ lo)
    {F : Space n → ℂ} (hc : ContinuousOn F (shell lo hi))
    {Y : Sphere n → ℂ} (hY : Continuous Y) :
    ContinuousOn (fun r : ℝ ↦ ∫ σ : Sphere n, F (r • (σ : Space n)) * Y σ ∂surfaceMeasure n)
      (Ioo lo hi) := by
  let : LocallyCompactSpace (Ioo lo hi) := isOpen_Ioo.locallyCompactSpace
  let : IsFiniteMeasure (surfaceMeasure n) := by unfold surfaceMeasure; infer_instance
  let scale : Ioo lo hi × Sphere n → Space n := fun p ↦ (p.1 : ℝ) • (p.2 : Space n)
  have hsc : Continuous scale :=
    (continuous_subtype_val.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)
  have hmem (p : Ioo lo hi × Sphere n) : scale p ∈ shell lo hi := by
    have hσ : ‖(p.2 : Space n)‖ = 1 := mem_sphere_zero_iff_norm.mp p.2.property
    change lo < ‖(p.1 : ℝ) • (p.2 : Space n)‖ ∧ ‖(p.1 : ℝ) • (p.2 : Space n)‖ < hi
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hlo.trans_lt p.1.property.1), hσ, mul_one]
    exact p.1.property
  have hprod : Continuous (fun p : Ioo lo hi × Sphere n ↦ F (scale p) * Y p.2) :=
    (hc.comp_continuous hsc hmem).mul (hY.comp continuous_snd)
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun r : Ioo lo hi ↦ ∫ σ : Sphere n, F ((r : ℝ) • (σ : Space n)) * Y σ ∂surfaceMeasure n)
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ := surfaceMeasure n)
      (f := fun r : Ioo lo hi ↦ fun σ : Sphere n ↦ F ((r : ℝ) • (σ : Space n)) * Y σ)
      hprod isCompact_univ)

/-- The actual surface integral, including its Jacobian, varies continuously
inside the shell. -/
theorem continuousOn_surfaceIntegral {n : ℕ} {lo hi : ℝ} (hlo : 0 ≤ lo)
    {F : Space n → ℂ} (hc : ContinuousOn F (shell lo hi)) :
    ContinuousOn (surfaceIntegral F) (Ioo lo hi) := by
  have hmean := continuousOn_angular_integral hlo hc (Y := fun _ ↦ (1 : ℂ)) continuous_const
  simp only [mul_one] at hmean
  exact (continuous_id.pow (n-1)).continuousOn.smul hmean


end Runcorn
