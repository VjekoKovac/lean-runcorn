module

public import Runcorn.MomentNecessity
public import Runcorn.LowAngularForm
public import Runcorn.Orthogonality
public import Runcorn.Varying

/-! # All subannuli force every constrained angular coefficient to vanish

The fixed-annulus necessity argument is applied directly to a spherical harmonic
of the chosen degree. This avoids choosing a basis in the varying-annuli theorem.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate
namespace Runcorn

/-- The partial radius range of Theorem 1 gives a square-integrable restriction
to every compact subannulus. -/
theorem continuousOn_shell_memLp {n : ℕ} {lo hi a b : ℝ} {f : Space n → ℂ}
    (hf : ContinuousOn f (shell lo hi)) (ha : lo < a) (hb : b < hi) :
    MemLp f 2 (volume.restrict (annulus a b)) := by
  have hc : ContinuousOn f (annulus a b) :=
    hf.mono fun _ hx ↦ ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hK := isCompact_annulus (n := n) a b
  exact (memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable hK.measurableSet)).mpr
    ((hc.norm.pow 2).integrableOn_compact hK)

/-- Vanishing of all shell tests implies the angular integral is zero at each
single radius whenever the degree has even one admissible moment exponent. -/
theorem angularIntegral_zero_from_all_tests {n k : ℕ} (hn : 2 ≤ n)
    {lo hi : ℝ} (hlo : 0 < lo) {f : Space n → ℂ} (hf : ContinuousOn f (shell lo hi))
    (ht : AllAnnularTests lo hi f) {Y : Sphere n → ℂ} (hY : IsSphericalHarmonic k Y)
    (hex : ∃ m, momentExponent n k m) :
    ∀ r ∈ Ioo lo hi, angularIntegral f Y r = 0 := by
  obtain ⟨m, hm⟩ := hex
  apply coefficient_zero_of_all_laurent_moments hlo.le
    (continuousOn_angular_integral hlo.le hf hY.continuous) (m + ((n-1 : ℕ) : ℤ))
  intro a b ha hab hb
  have ha0 := hlo.trans ha
  change (∫ t in a..b, angularIntegral f Y t * (t : ℂ) ^ (m + ((n-1 : ℕ) : ℤ))) = 0
  rw [← radial_moment_eq_intervalIntegral n ha0 hab.le (angularIntegral f Y) m]
  have hf₂ := continuousOn_shell_memLp hf ha hb
  have hsep : ∀ e : ℤ, momentExponent n k e →
      (∫ x in annulus a b, f x * atDirection Y x * ((‖x‖ ^ e : ℝ) : ℂ)) = 0 := by
    intro e he
    obtain ⟨p,q,hp,hq,rfl,rfl⟩ := (momentExponent_iff_special_pair hn e).mp he
    apply annular_test_zero_on_span ha0 hf₂ _ _ (sphericalHarmonic_mem_nullPower_span hn hY)
    intro ζ hz
    exact special_pair_test_zero hn hp hq ha0 (ht a b ha hab hb) ζ hz
      (specialPair_admissible hn hq hlo ζ hz)
  simpa using ((separatedTests_iff_normalized_moments hn ha0 hf₂ hY.continuous
    (one_ne_zero : (1:ℂ) ≠ 0)).mp hsep m hm)

/-- Existence of the continuous spherical slice in the actual low-degree span,
simultaneously at every interior radius. -/
theorem slices_mem_lowAngularSpan_of_all_tests {n : ℕ} (hn : 2 ≤ n)
    {lo hi : ℝ} (hlo : 0 < lo) {f : Space n → ℂ} (hf : ContinuousOn f (shell lo hi))
    (ht : AllAnnularTests lo hi f) (r : ℝ) (hr : r ∈ Ioo lo hi) :
    ∃ F : C(Sphere n,ℂ), F ∈ lowAngularSpan n (if n = 2 then 2 else 1) ∧
      ∀ σ : Sphere n, F σ = f (r • σ.val) := by
  have hr0 : 0 < r := hlo.trans hr.1
  let F : C(Sphere n, ℂ) := ⟨fun σ ↦ f (r • σ.val),
    hf.comp_continuous (f := fun σ : Sphere n ↦ r • σ.val) (by fun_prop) fun σ ↦ by
      change lo < ‖r • σ.val‖ ∧ ‖r • σ.val‖ < hi
      rw [norm_polarPoint_of_sphere r hr0 σ]
      exact hr⟩
  refine ⟨F, mem_lowAngularSpan_of_high_moments (by omega) (by split <;> omega) F ?_ ?_, fun _ ↦ rfl⟩
  · intro p q Y Z hpq hY hZ
    exact integral_mul_eq_zero_of_degree_ne hn hpq.symm hZ hY.conj
  · intro k Y hk hY
    apply angularIntegral_zero_from_all_tests hn hlo hf ht hY.conj _ r hr
    by_cases he : n = 2
    · subst n
      simp only [ite_true] at hk
      exact ⟨_, terminal_moment_in_plane hk⟩
    · simp only [he, ite_false] at hk
      exact ⟨_, terminal_moment_in_higher_dimension (by omega) hk⟩

/-- The necessity direction of Theorem 1 with the exceptional two-dimensional
three-mode conclusion. All sphere tests, basis choices and projections have
been eliminated from the hypotheses. -/
theorem angularForm_of_allAnnularTests {n : ℕ} (hn : 2 ≤ n)
    {lo hi : ℝ} (hlo : 0 < lo) {f : Space n → ℂ} (hf : ContinuousOn f (shell lo hi))
    (ht : AllAnnularTests lo hi f) : AngularForm lo hi f := by
  have hs := slices_mem_lowAngularSpan_of_all_tests hn hlo hf ht
  constructor
  · intro hng
    apply radialOn_of_lowAngularSpan hlo
    simpa [show n ≠ 2 by omega] using hs
  · rintro rfl
    apply threeModes_of_lowAngularSpan hlo hf
    simpa using hs

end Runcorn
