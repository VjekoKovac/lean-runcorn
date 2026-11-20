module

public import Runcorn.Separated

/-! # Polar transport of the L² space of the annulus

The polar parametrization has a measurable inverse on the positive-radius
support of the product measure. Its pushforward is Lebesgue measure restricted
to the closed annulus. This yields equivalence of membership in L² and exact
equality of the L² errors in Cartesian and polar coordinates.
-/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory Metric

namespace Runcorn

instance finiteRadialMeasure (n : ℕ) (a b : ℝ) : IsFiniteMeasure (radialMeasure n a b) := by
  have h : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1)) (Icc a b) :=
    (continuous_id.pow _).continuousOn.integrableOn_compact isCompact_Icc
  exact isFiniteMeasure_withDensity_ofReal h.hasFiniteIntegral

def polarMap (n : ℕ) (p : ℝ × Sphere n) : Space n := p.1 • (p.2 : Space n)

theorem measurable_polarMap (n : ℕ) : Measurable (polarMap n) :=
  (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).measurable

theorem ae_radial_mem (n : ℕ) (a b : ℝ) :
    ∀ᵐ r ∂radialMeasure n a b, r ∈ Icc a b :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

theorem ae_polar_positive {n : ℕ} {a b : ℝ} (ha : 0 < a) :
    ∀ᵐ p : ℝ × Sphere n ∂(radialMeasure n a b).prod (surfaceMeasure n), 0 < p.1 := by
  have : SFinite (surfaceMeasure n) := by unfold surfaceMeasure; infer_instance
  exact Measure.quasiMeasurePreserving_fst.tendsto_ae (by
    filter_upwards [ae_radial_mem n a b] with r hr using ha.trans_le hr.1)

theorem measurePreserving_polarMap {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} (ha : 0 < a) :
    MeasurePreserving (polarMap n) ((radialMeasure n a b).prod (surfaceMeasure n))
      (volume.restrict (annulus a b)) := by
  have : IsFiniteMeasure (surfaceMeasure n) := by unfold surfaceMeasure; infer_instance
  have : IsFiniteMeasure (volume.restrict (annulus (n := n) a b)) :=
    isFiniteMeasure_restrict.mpr (isCompact_annulus a b).measure_lt_top.ne
  refine ⟨measurable_polarMap n, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply (measurable_polarMap n) hs, ← measureReal_eq_measureReal_iff]
  let A := s.indicator (fun _ : Space n ↦ (1 : ℂ))
  let B := (polarMap n ⁻¹' s).indicator (fun _ : ℝ × Sphere n ↦ (1 : ℂ))
  have hB : B = A ∘ polarMap n := by
    funext x
    exact Set.indicator_comp_right (g := fun _ : Space n ↦ (1 : ℂ)) (polarMap n)
  have hA : IntegrableOn A (annulus a b) := (integrable_const _).indicator hs
  have hb : Integrable B ((radialMeasure n a b).prod (surfaceMeasure n)) :=
    (integrable_const _).indicator ((measurable_polarMap n) hs)
  have hid : (∫ x in annulus a b, A x) =
      ∫ p, B p ∂(radialMeasure n a b).prod (surfaceMeasure n) := by
    rw [integral_annulus_polar hn ha hA, integral_prod _ hb, integral_radialMeasure n ha, hB]
    rfl
  rw [integral_indicator_const _ hs, integral_indicator_const _ ((measurable_polarMap n) hs),
    Complex.real_smul, Complex.real_smul, mul_one, mul_one, Complex.ofReal_inj] at hid
  exact hid.symm

/-- A measurable inverse, with a unit vector supplied at the unused origin. -/
def polarInverse (n : ℕ) (hn : 2 ≤ n) (x : Space n) : ℝ × Sphere n := by
  classical
  refine (‖x‖, ⟨if x = 0 then EuclideanSpace.single ⟨0, by omega⟩ 1 else ‖x‖⁻¹ • x, ?_⟩)
  split <;> simp_all [norm_smul]

theorem measurable_polarInverse (n : ℕ) (hn : 2 ≤ n) : Measurable (polarInverse n hn) := by
  classical
  apply continuous_norm.measurable.prodMk
  apply Measurable.subtype_mk
  exact Measurable.ite (measurableSet_singleton (0 : Space n)) measurable_const
    (continuous_norm.measurable.inv.smul measurable_id)

theorem polarInverse_polarMap {n : ℕ} (hn : 2 ≤ n) (p : ℝ × Sphere n) (hr : 0 < p.1) :
    polarInverse n hn (polarMap n p) = p := by
  have hnrm := norm_polarPoint_of_sphere p.1 hr p.2
  have hx := norm_pos_iff.mp (hnrm.symm ▸ hr)
  apply Prod.ext
  · exact hnrm
  · apply Subtype.ext
    simp [polarInverse, polarMap, hx, hnrm, smul_smul, hr.ne']

theorem polarMap_polarInverse {n : ℕ} (hn : 2 ≤ n) (x : Space n) :
    polarMap n (polarInverse n hn x) = x := by
  by_cases hx : x = 0
  · simp [hx, polarMap, polarInverse]
  · simp [polarMap, polarInverse, hx, smul_smul]

theorem measurePreserving_polarInverse {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} (ha : 0 < a) :
    MeasurePreserving (polarInverse n hn) (volume.restrict (annulus a b))
      ((radialMeasure n a b).prod (surfaceMeasure n)) := by
  refine ⟨measurable_polarInverse n hn, ?_⟩
  rw [← (measurePreserving_polarMap hn ha).map_eq,
    Measure.map_map (measurable_polarInverse n hn) (measurable_polarMap n)]
  calc
    _ = Measure.map id ((radialMeasure n a b).prod (surfaceMeasure n)) := by
      apply Measure.map_congr
      filter_upwards [ae_polar_positive ha] with p hp using polarInverse_polarMap hn p hp
    _ = _ := Measure.map_id

theorem memLp_polar_iff {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} (ha : 0 < a)
    {f : Space n → ℂ} {p : ENNReal} :
    MemLp (f ∘ polarMap n) p ((radialMeasure n a b).prod (surfaceMeasure n)) ↔
      MemLp f p (volume.restrict (annulus a b)) := by
  constructor
  · intro hf
    have := hf.comp_measurePreserving (measurePreserving_polarInverse hn ha)
    simpa only [Function.comp_def, polarMap_polarInverse] using this
  · exact fun h ↦ h.comp_measurePreserving (measurePreserving_polarMap hn ha)

theorem eLpNorm_polar {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} (ha : 0 < a)
    {f : Space n → ℂ} (hf : AEStronglyMeasurable f (volume.restrict (annulus a b))) (p : ENNReal) :
    eLpNorm (f ∘ polarMap n) p ((radialMeasure n a b).prod (surfaceMeasure n)) =
      eLpNorm f p (volume.restrict (annulus a b)) :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_polarMap hn ha)

end Runcorn
