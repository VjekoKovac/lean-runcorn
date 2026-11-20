module

public import Runcorn.HighMoments
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Separated tests for the low modes in Theorem 1

These are the tests needed by the fixed-annulus sufficiency argument. The
conversion from polar angles to the planar unit sphere is pointwise. 
-/

@[expose] public section
noncomputable section
open Set MeasureTheory MvPolynomial
namespace Runcorn

private theorem circleDirection_surj : Function.Surjective circleDirection := by
  intro σ
  let z : ℂ := ⟨σ.val 0, σ.val 1⟩
  have hsq := EuclideanSpace.real_norm_sq_eq σ.val
  rw [norm_eq_of_mem_sphere σ, one_pow, Fin.sum_univ_two] at hsq
  have hz : ‖z‖ = 1 := by
    have h := Complex.sq_norm z
    simp [z, Complex.normSq_apply, ← sq] at h
    nlinarith [hsq, norm_nonneg z]
  have hx : Real.cos z.arg = σ.val 0 := by
    rw [Complex.cos_arg (by intro h; simp [h] at hz), hz, div_one]
  have hy : Real.sin z.arg = σ.val 1 := by rw [Complex.sin_arg, hz, div_one]
  refine ⟨z.arg, Subtype.ext (PiLp.ext fun i ↦ ?_)⟩
  fin_cases i <;> simp [circleDirection, polarPoint, hx, hy]

private theorem lowSpan_const {n d : ℕ} (hd : 0 < d) (c : ℂ) :
    ContinuousMap.const (Sphere n) c ∈ lowAngularSpan n d := by
  refine Submodule.subset_span ⟨0,hd,C c,isHomogeneous_C _ c, harmonic_polynomialValue _ ?_, ?_⟩
  · simp [Polynomial.lap]
  · simp [polynomialValue]

private theorem lowSpan_coord {n d : ℕ} (hd : 1 < d) (i : Fin n) :
    polynomialOnSphere (X i : MvPolynomial (Fin n) ℂ) ∈ lowAngularSpan n d := by
  refine Submodule.subset_span ⟨1,hd,X i,isHomogeneous_X _ i,
    harmonic_polynomialValue _ (Polynomial.lap_low_degree _ (isHomogeneous_X _ i) (by decide)), fun _ ↦ rfl⟩

/-- An angular form satisfying Theorem 1(iii) belongs on every sphere to the
span of the surviving harmonic degrees. -/
theorem low_slices_of_angularForm {n : ℕ} (hn : 2 ≤ n) {lo hi : ℝ} (hlo : 0 < lo)
    {f : Space n → ℂ} (hform : AngularForm lo hi f) (r : ℝ) (hr : r ∈ Ioo lo hi) :
    ∃ F : C(Sphere n,ℂ), F ∈ lowAngularSpan n (if n = 2 then 2 else 1) ∧
      ∀ σ : Sphere n, F σ = f (r • σ.val) := by
  by_cases h : n = 2
  · subst n
    obtain ⟨gM,c,gP,_,_,_,hform⟩ := hform.2 rfl
    let A := gM r + gP r
    let B := (gP r - gM r) * Complex.I
    let L (i : Fin 2) := polynomialOnSphere (X i : MvPolynomial (Fin 2) ℂ)
    refine ⟨ContinuousMap.const _ (c r) + A • L 0 + B • L 1, ?_, ?_⟩
    · simp only [ite_true]
      exact Submodule.add_mem _ (Submodule.add_mem _ (lowSpan_const (by decide) _)
        (Submodule.smul_mem _ _ (lowSpan_coord (by decide) _)))
        (Submodule.smul_mem _ _ (lowSpan_coord (by decide) _))
    · intro σ
      obtain ⟨φ,rfl⟩ := circleDirection_surj σ
      have he : r • (circleDirection φ).val = polarPoint 2 r φ := by
        ext i; fin_cases i <;> simp [circleDirection, polarPoint]
      rw [he, hform r hr φ]
      have heP : Complex.exp (Complex.I * (φ : ℂ)) =
          (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I := by rw [mul_comm, Complex.exp_ofReal_mul_I]
      have heM : Complex.exp (-Complex.I * (φ : ℂ)) =
          (Real.cos φ : ℂ) - (Real.sin φ : ℂ) * Complex.I := by
        rw [show -Complex.I * (φ : ℂ) = (-φ : ℝ) * Complex.I by push_cast; ring,
          Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
        ring
      rw [heM, heP]
      simp [A, B, L, polynomialOnSphere, polynomialValue, circleDirection, polarPoint,
        smul_eq_mul]
      ring
  · obtain ⟨g,hg⟩ := hform.1 (by omega)
    refine ⟨ContinuousMap.const _ (g r), ?_, fun σ ↦ ?_⟩
    · simpa [h] using lowSpan_const (n := n) (d := 1) (by decide) (g r)
    · have hnorm := norm_polarPoint_of_sphere r (hlo.trans hr.1) σ
      have hx : r • σ.val ∈ shell lo hi := by
        change lo < ‖r • σ.val‖ ∧ ‖r • σ.val‖ < hi
        rwa [hnorm]
      change g r = f (r • σ.val)
      simpa only [hnorm] using (hg (r • σ.val) hx).symm

/-- The high-degree spherical harmonics annihilate every slice in the surviving
low-degree span. Both factors enter bilinearly. -/
theorem lowAngularSpan_pairing_zero {n d k : ℕ} (hn : 2 ≤ n) (hk : d ≤ k)
    {F : C(Sphere n,ℂ)} (hF : F ∈ lowAngularSpan n d)
    {Y : Sphere n → ℂ} (hY : IsSphericalHarmonic k Y) :
    (∫ σ, F σ * Y σ ∂surfaceMeasure n) = 0 := by
  let : IsFiniteMeasure (surfaceMeasure n) := by unfold surfaceMeasure; infer_instance
  have hi (Z : C(Sphere n,ℂ)) : Integrable (fun σ ↦ Z σ * Y σ) (surfaceMeasure n) :=
    (Z.continuous.mul hY.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply Submodule.span_induction (p := fun Z _ ↦ (∫ σ, Z σ * Y σ ∂surfaceMeasure n) = 0)
    ?_ ?_ ?_ ?_ hF
  · rintro Z ⟨p,hp,hZ⟩
    exact integral_mul_eq_zero_of_degree_ne hn (by omega) hZ hY
  · simp
  · intro Z Z' _ _ hZ hZ'
    simp only [ContinuousMap.add_apply, add_mul]
    rw [integral_add (hi Z) (hi Z'), hZ, hZ', add_zero]
  · intro c Z _ hZ
    simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul, hZ, mul_zero]

/-- Item (iii) of Theorem 1 supplies every separated annular moment needed
for an arbitrary homogeneous interior mode and exterior Kelvin mode. -/
theorem separated_tests_of_angularForm {n : ℕ} (hn : 2 ≤ n)
    {lo hi a b : ℝ} (hlo : 0 < lo) (ha : lo < a) (hb : b < hi)
    {f : Space n → ℂ} (hf : ContinuousOn f (shell lo hi)) (hform : AngularForm lo hi f)
    (k : ℕ) (Y : Sphere n → ℂ) (hY : IsSphericalHarmonic k Y) (m : ℤ)
    (hm : momentExponent n k m) :
    (∫ x in annulus a b, f x * atDirection Y x * ((‖x‖^m : ℝ) : ℂ)) = 0 := by
  rw [annular_pairing_eq_radial_moment hn (hlo.trans ha) f Y m
    (integrableOn_separatedTest (hlo.trans ha) (continuousOn_shell_memLp hf ha hb) hY.continuous m),
    integral_radialMeasure n (hlo.trans ha)]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro r hr
  obtain ⟨F,hF,hFσ⟩ := low_slices_of_angularForm hn hlo hform r ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  have hk : (if n = 2 then 2 else 1) ≤ k := by
    obtain ⟨p,q,hp,hqp,rfl,_⟩ := (momentExponent_iff_special_pair hn _).mp hm
    split <;> omega
  have hzero := lowAngularSpan_pairing_zero hn hk hF hY
  simp only [hFσ] at hzero
  simp [angularIntegral, hzero]

end Runcorn
