module

public import Runcorn.Expansion
public import Runcorn.Fixed
public import Runcorn.TestRegularity

/-!
# Separated tests on the closed annulus

For square-integrable input the comparison between annular tests by a Laurent
monomial times a spherical function and the radial moments of its angular
coefficient holds for every continuous angular function. Compactness supplies
the integrability needed for the Bochner integrals.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Metric
open scoped ComplexConjugate

namespace Runcorn

/-- A continuous angular function extends continuously along rays off the origin. -/
theorem continuousOn_atDirection {n : ℕ} {Y : Sphere n → ℂ} (hY : Continuous Y) :
    ContinuousOn (atDirection Y) ({0}ᶜ : Set (Space n)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let T := homeomorphUnitSphereProd (Space n)
  have hc := hY.comp (continuous_fst.comp T.continuous)
  apply hc.congr
  intro x
  have hσ : ‖(x : Space n)‖⁻¹ • (x : Space n) ∈ sphere (0 : Space n) 1 := by
    simpa only [T, ← homeomorphUnitSphereProd_apply_fst_coe] using (T x).1.property
  simp only [Set.domRestrict_apply, Function.comp_apply, atDirection, dite_eq_left hσ]
  exact congrArg Y (Subtype.ext (homeomorphUnitSphereProd_apply_fst_coe _ x))

/-- An L² function on the shell can be paired with any continuous angular factor
and any Laurent monomial. Positivity of the inner radius removes the pole. -/
theorem integrableOn_separatedTest {n : ℕ} {a b : ℝ} (ha : 0 < a) {f : Space n → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulus a b))) {Y : Sphere n → ℂ}
    (hY : Continuous Y) (m : ℤ) :
    IntegrableOn (fun x : Space n ↦ f x * atDirection Y x * ((‖x‖ ^ m : ℝ) : ℂ))
      (annulus a b) := by
  have hK := isCompact_annulus (n := n) a b
  have : IsFiniteMeasure (volume.restrict (annulus (n := n) a b)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hdir : ContinuousOn (atDirection Y) (annulus a b) := by
    apply (continuousOn_atDirection hY).mono
    intro x hx
    exact norm_pos_iff.mp (ha.trans_le hx.1)
  have hpow : ContinuousOn (fun x : Space n ↦ ((‖x‖ ^ m : ℝ) : ℂ)) (annulus a b) := by
    refine Complex.continuous_ofReal.comp_continuousOn (continuous_norm.continuousOn.zpow₀ m ?_)
    exact fun _ hx ↦ Or.inl (ha.trans_le hx.1).ne'
  have hL1 : IntegrableOn f (annulus a b) := hf.integrable (by norm_num)
  exact (hL1.mul_continuousOn hdir hK).mul_continuousOn hpow hK

/-- After integration over the sphere, vanishing of all separated monomial
tests is exactly the radial orthogonality in the theorem. The coefficient may
be divided by any nonzero scalar, in particular the squared norm of a basis vector. -/
theorem separatedTests_iff_normalized_moments {n k : ℕ} (hn : 2 ≤ n)
    {a b : ℝ} (ha : 0 < a) {f : Space n → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulus a b))) {Y : Sphere n → ℂ}
    (hY : Continuous Y) {c : ℂ} (hc : c ≠ 0) :
    (∀ m : ℤ, momentExponent n k m →
      (∫ x in annulus a b, f x * atDirection Y x * ((‖x‖ ^ m : ℝ) : ℂ)) = 0) ↔
    (∀ m : ℤ, momentExponent n k m →
      (∫ r, (angularIntegral f Y r / c) * ((r ^ m : ℝ) : ℂ) ∂radialMeasure n a b) = 0) := by
  simp_rw [annular_pairing_eq_radial_moment hn ha f Y _ (integrableOn_separatedTest ha hf hY _),
    normalized_radial_moment_eq_zero_iff _ _ _ _ hc]

end Runcorn
