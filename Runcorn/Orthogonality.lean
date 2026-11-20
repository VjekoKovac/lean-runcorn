module

public import Runcorn.PolynomialCalculus
public import Runcorn.PolynomialHomogeneity
public import Runcorn.Fixed
public import Runcorn.Cutoff
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Green's identity for homogeneous harmonic polynomials on the sphere -/

@[expose] public section
noncomputable section
open Filter MeasureTheory MvPolynomial Set Metric
open scoped Topology ComplexConjugate
namespace Runcorn
variable {n : ℕ}
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

private def wronskian (P Q : Polynomial.Poly n) (i : Fin n) : Polynomial.Poly n :=
  P * pderiv i Q - Q * pderiv i P

private theorem divergence_wronskian (P Q : Polynomial.Poly n) :
    ∑ i, pderiv i (wronskian P Q i) = P * Polynomial.lap Q - Q * Polynomial.lap P := by
  simp only [Polynomial.lap, wronskian, map_sub, pderiv_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem radial_wronskian {p q : ℕ} {P Q : Polynomial.Poly n} (hP : P.IsHomogeneous p)
    (hQ : Q.IsHomogeneous q) (x : Space n) :
    ∑ i, (x i : ℂ) * polynomialValue (wronskian P Q i) x =
      ((q : ℂ) - p) * polynomialValue P x * polynomialValue Q x := by
  have euler (H : Polynomial.Poly n) (k : ℕ) (hH : H.IsHomogeneous k) :
      ∑ i, (x i : ℂ) * polynomialValue (pderiv i H) x = k * polynomialValue H x := by
    simpa [polynomialValue, nsmul_eq_mul] using
      congrArg (eval fun i => (x i : ℂ)) hH.sum_X_mul_pderiv
  calc
    _ = polynomialValue P x * (∑ i, (x i : ℂ) * polynomialValue (pderiv i Q) x) -
        polynomialValue Q x * (∑ i, (x i : ℂ) * polynomialValue (pderiv i P) x) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp [wronskian, polynomialValue]
      ring
    _ = _ := by rw [euler Q q hQ, euler P p hP]; ring

private theorem greens_identity (P Q : Polynomial.Poly n)
    (hP : InnerProductSpace.HarmonicOnNhd (polynomialValue P) univ)
    (hQ : InnerProductSpace.HarmonicOnNhd (polynomialValue Q) univ)
    (u : Space n → ℂ) (hu : ContDiff ℝ 1 u) (hcu : HasCompactSupport u) :
    (∫ x, ∑ i, fderiv ℝ u x (e i) * polynomialValue (wronskian P Q i) x) = 0 := by
  let W := wronskian P Q
  have hW (i : Fin n) := contDiff_polynomialValue (W i) 1
  have A (i : Fin n) : Integrable (fun x => fderiv ℝ u x (e i) * polynomialValue (W i) x) := by
    apply Continuous.integrable_of_hasCompactSupport _ ((hcu.fderiv_apply (𝕜 := ℝ) (e i)).mul_right)
    exact ((hu.continuous_fderiv (by decide)).clm_apply continuous_const).mul (hW i).continuous
  have B (i : Fin n) : Integrable (fun x => u x * fderiv ℝ (polynomialValue (W i)) x (e i)) := by
    simp_rw [show ∀ x, fderiv ℝ (polynomialValue (W i)) x (e i) =
      polynomialValue (pderiv i (W i)) x from polynomialValue_partial (W i) i]
    exact (hu.continuous.mul (contDiff_polynomialValue _ 1).continuous).integrable_of_hasCompactSupport
      hcu.mul_right
  have ibp (i : Fin n) := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (A i) (B i)
    ((hu.continuous.mul (hW i).continuous).integrable_of_hasCompactSupport hcu.mul_right)
    (fun x _ => hu.differentiable (by decide) x) (fun x _ => (hW i).differentiable (by decide) x)
  have hz (x : Space n) : (∑ i, fderiv ℝ (polynomialValue (W i)) x (e i)) = 0 := by
    simp_rw [polynomialValue_partial]
    change ∑ i, eval _ (pderiv i (W i)) = _
    rw [← map_sum, divergence_wronskian, map_sub, map_mul, map_mul]
    have hr (H : Polynomial.Poly n) (hh : InnerProductSpace.HarmonicOnNhd (polynomialValue H) univ) :
        polynomialValue (Polynomial.lap H) x = 0 := by
      rw [← laplacian_polynomialValue]
      exact (hh x trivial).2.self_of_nhds
    change polynomialValue P x * polynomialValue (Polynomial.lap Q) x -
      polynomialValue Q x * polynomialValue (Polynomial.lap P) x = 0
    rw [hr P hP, hr Q hQ]; ring
  change (∫ x, ∑ i, fderiv ℝ u x (e i) * polynomialValue (W i) x) = _
  rw [integral_finsetSum _ fun i _ => A i]
  have he(i : Fin n) := congrArg Neg.neg (ibp i)
  simp only [neg_neg] at he
  simp_rw [← he]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => B i]
  simp only [← Finset.mul_sum, hz, mul_zero, integral_zero, neg_zero]

private theorem cutoffVolume {p q : ℕ} {P Q : Polynomial.Poly n}
    (hP : P.IsHomogeneous p) (hQ : Q.IsHomogeneous q) (hne : p ≠ q)
    (hpH : InnerProductSpace.HarmonicOnNhd (polynomialValue P) univ)
    (hqH : InnerProductSpace.HarmonicOnNhd (polynomialValue Q) univ)
    {c : ℝ → ℝ} (hc : ContDiff ℝ 1 c) (hc0 : ∀ s : ℝ, 4 ≤ s → c s = 0) :
    (∫ x : Space n, Complex.ofReal (deriv c (‖x‖^2)) * polynomialValue P x * polynomialValue Q x) = 0 := by
  let φ : Space n → ℂ := fun x => ↑(c (‖x‖^2))
  have hφ : ContDiff ℝ 1 φ :=
    Complex.ofRealCLM.contDiff.comp (hc.comp (contDiff_norm_sq ℝ))
  have hφc : HasCompactSupport φ := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space n) 2)
    intro x hx
    contrapose! hx
    have hr : 2 < ‖x‖ := by simpa using hx
    have h4 : 4 ≤ ‖x‖^2 := by nlinarith [mul_pos (sub_pos.mpr hr) (show 0 < ‖x‖ + 2 by positivity)]
    simp [φ, Function.mem_support, hc0 _ h4]
  have hcoord (x : Space n) (i : Fin n) :
      fderiv ℝ φ x (e i) = 2 * Complex.ofReal (deriv c (‖x‖^2)) * (x i : ℂ) := by
    have hd := Complex.ofRealCLM.hasFDerivAt.comp x
      (((hc.differentiable (by decide) _).hasDerivAt).comp_hasFDerivAt x
        (hasStrictFDerivAt_norm_sq x).hasFDerivAt)
    change fderiv ℝ (Complex.ofRealCLM ∘ c ∘ (fun x : Space n => ‖x‖^2)) x (e i) = _
    rw [hd.fderiv]
    simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]
    ring
  have hpt (x : Space n) :
      (∑ i, fderiv ℝ φ x (e i) * polynomialValue (wronskian P Q i) x) =
      (2 * ((q : ℂ)-p)) * (Complex.ofReal (deriv c (‖x‖^2)) * polynomialValue P x * polynomialValue Q x) := by
    simp_rw [hcoord x]
    simp_rw [mul_assoc (2 * Complex.ofReal (deriv c _))]
    rw [← Finset.mul_sum, radial_wronskian hP hQ]
    ring
  have hv := greens_identity P Q hpH hqH φ hφ hφc
  simp_rw [hpt] at hv
  rw [integral_const_mul] at hv
  exact (mul_eq_zero.mp hv).resolve_left (mul_ne_zero (by norm_num)
    (sub_ne_zero.mpr (by exact_mod_cast hne.symm)))

/-- Homogeneous spherical harmonics of unequal degrees are orthogonal for the
bilinear angular pairing. Conjugation of a harmonic gives the Hilbert-space version. -/
theorem integral_mul_eq_zero_of_degree_ne {p q : ℕ} (hn : 2 ≤ n) (hne : p ≠ q)
    {Y Z : Sphere n → ℂ} (hY : IsSphericalHarmonic p Y) (hZ : IsSphericalHarmonic q Z) :
    (∫ σ, Y σ * Z σ ∂surfaceMeasure n) = 0 := by
  obtain ⟨P, hp, hpH, hP⟩ := hY
  obtain ⟨Q, hq, hqH, hQ⟩ := hZ
  obtain ⟨c, hc, hc0, hcd, hcm⟩ := exists_orthogonality_cutoff
  let F : Space n → ℂ := fun x => Complex.ofReal (deriv c (‖x‖^2)) *
    polynomialValue P x * polynomialValue Q x
  let m := n-1+p+q
  have hF : Continuous F :=
    ((Complex.continuous_ofReal.comp ((hc.continuous_deriv (by decide)).comp
      (continuous_norm.pow 2))).mul (contDiff_polynomialValue P 1).continuous).mul
      (contDiff_polynomialValue Q 1).continuous
  have hFc : IntegrableOn F (annulus 1 2) := by
    have hcompact : IsCompact (annulus (n:=n) 1 2) := by
      apply (isCompact_closedBall (0 : Space n) 2).of_isClosed_subset
        (isClosed_Icc.preimage continuous_norm)
      exact fun x hx => mem_closedBall_zero_iff.mpr hx.2
    exact hF.continuousOn.integrableOn_compact hcompact
  have hrest : (∫ x in annulus 1 2, F x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact cutoffVolume hp hq hne hpH hqH hc hc0
    · intro x hx
      have hs : ‖x‖^2 ∉ Icc (1 : ℝ) 4 := by
        intro ht
        apply hx
        constructor <;> nlinarith [ht.1, ht.2, norm_nonneg x]
      simp [F, hcd _ hs]
  let z := ∫ σ, Y σ * Z σ ∂surfaceMeasure n
  have pull (r : ℝ) (hr : r ∈ Icc (1:ℝ) 2) :
      r ^ (n-1) • (∫ σ : Sphere n, F (r • σ.val) ∂surfaceMeasure n) =
      Complex.ofReal (deriv c (r^2) * r^m) * z := by
    have hr0 : 0 ≤ r := by linarith [hr.1]
    have hg (σ : Sphere n) : F (r • σ.val) =
        (Complex.ofReal (deriv c (r^2)) * (r : ℂ)^p * (r : ℂ)^q) * (Y σ * Z σ) := by
      dsimp [F]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0, mem_sphere_zero_iff_norm.mp σ.prop, mul_one,
        polynomialValue_smul_of_homogeneous P hp, polynomialValue_smul_of_homogeneous Q hq, hP σ, hQ σ]
      ring
    simp_rw [hg]
    rw [integral_const_mul]
    simp only [m, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_mul, pow_add, z]
    ring
  rw [integral_annulus_polar hn (by norm_num) hFc, setIntegral_congr_fun measurableSet_Icc pull,
    integral_mul_const, integral_complex_ofReal] at hrest
  exact (mul_eq_zero.mp hrest).resolve_left (Complex.ofReal_ne_zero.mpr (hcm m))

end Runcorn
