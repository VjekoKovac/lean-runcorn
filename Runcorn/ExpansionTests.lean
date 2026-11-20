module

public import Runcorn.FiniteMoments
public import Runcorn.PairingLimit
public import Runcorn.ModeTests

/-! # The sufficiency direction for the special harmonic pairs

An expansion with the stated moments annihilates every separated spherical
test of the permitted degree and every product of gradients of an interior
homogeneous harmonic polynomial and an exterior Kelvin mode.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter

namespace Runcorn

theorem memLp_separatedWeight {n : ℕ} {a b : ℝ} (ha : 0 < a)
    (Y : Sphere n → ℂ) (hY : Continuous Y) (m : ℤ) :
    MemLp (fun x : Space n ↦ atDirection Y x * ((‖x‖ ^ m : ℝ) : ℂ)) 2
      (volume.restrict (annulus a b)) := by
  have hK := isCompact_annulus (n := n) a b
  have : IsFiniteMeasure (volume.restrict (annulus (n := n) a b)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hdir : ContinuousOn (atDirection Y) (annulus a b) :=
    (continuousOn_atDirection hY).mono fun _ hx ↦ norm_pos_iff.mp (ha.trans_le hx.1)
  have hpow : ContinuousOn (fun x : Space n ↦ ((‖x‖ ^ m : ℝ) : ℂ)) (annulus a b) :=
    Complex.continuous_ofReal.comp_continuousOn (continuous_norm.continuousOn.zpow₀ m
      fun _ hx ↦ Or.inl (ha.trans_le hx.1).ne')
  have h := hdir.mul hpow
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn h
  exact MemLp.of_bound (h.aestronglyMeasurable hK.measurableSet) C
    (ae_restrict_of_forall_mem hK.measurableSet hC)

theorem hasMomentExpansion_separatedTests {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} (ha : 0 < a)
    {Y : AngularFamily n} (hY : IsAngularBasis Y) {f : Space n → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulus a b))) (hexp : HasMomentExpansion a b Y f)
    (k : ℕ) (Z : Sphere n → ℂ) (hZ : IsSphericalHarmonic k Z)
    (m : ℤ) (hm : momentExponent n k m) :
    (∫ x in annulus a b, f x * atDirection Z x * ((‖x‖ ^ m : ℝ) : ℂ)) = 0 := by
  obtain ⟨g, hg, hpart, hlim⟩ := hexp
  simp_rw [mul_assoc]
  apply integral_zero_of_L2_limit hpart hf (memLp_separatedWeight ha Z hZ.continuous m) hlim
  intro N
  simpa only [mul_assoc] using finiteExpansion_test_zero hn ha Y hY g hg N (hpart N) Z hZ hm

theorem hasMomentExpansion_homogeneousTest {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} (ha : 0 < a)
    {Y : AngularFamily n} (hY : IsAngularBasis Y) {f : Space n → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulus a b))) (hexp : HasMomentExpansion a b Y f)
    (p q : ℕ) (hp : 0 < p) (hq : n = 2 → 0 < q) (P Q : Polynomial.Poly n)
    (hP : P.IsHomogeneous p) (hQ : Q.IsHomogeneous q) (hΔP : Polynomial.lap P = 0)
    (hΔQ : Polynomial.lap Q = 0) :
    (∫ x in annulus a b, f x * gradDot (polynomialValue P) (kelvinMode q Q) x) = 0 :=
  homogeneous_test_zero_of_separated hn ha hf
    (hasMomentExpansion_separatedTests hn ha hY hf hexp) p q hp hq P Q hP hQ hΔP hΔQ

end Runcorn
