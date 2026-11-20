module

public import Runcorn.GradientDecomposition
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Weak maximum principle in every Euclidean dimension
At a local maximum of a C² real function, its second derivatives along the
coordinate lines are nonpositive. Adding a small positive multiple of the
squared radius therefore forces the maximum of a harmonic function to the
boundary of any compact set. Real linear functionals yield the complex
norm version used in approximation on balls and shells.
-/
@[expose] public section
noncomputable section
open Set Metric Filter InnerProductSpace Laplacian
open scoped Topology
namespace Runcorn
variable {n : ℕ}

private theorem deriv_deriv_nonpos_of_localMax {g : ℝ → ℝ} {t : ℝ}
    (hc : ContinuousAt g t) (hm : IsLocalMax g t) : deriv (deriv g) t ≤ 0 := by
  by_contra! h
  have hmin := isLocalMin_of_deriv_deriv_pos h hm.deriv_eq_zero hc
  have he : g =ᶠ[𝓝 t] fun _ => g t := by
    filter_upwards [hm,hmin] with y h1 h2
    exact le_antisymm h1 h2
  have hz := he.deriv.deriv_eq
  simp at hz
  exact (ne_of_gt h) hz

theorem laplacian_nonpos_of_localMax {f : Space n → ℝ} {x : Space n}
    (h : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) : Δ f x ≤ 0 := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_nonpos
  intro i _
  let v := EuclideanSpace.basisFun (Fin n) ℝ i
  let g := fun t : ℝ => x + t • v
  have hg (t : ℝ) : HasDerivAt g v t := by
    simpa [g] using ((hasDerivAt_id t).smul_const v).const_add x
  have he : g 0 = x := by simp [g]
  have ht : Tendsto g (𝓝 0) (𝓝 x) := he ▸ (hg 0).continuousAt
  have heq : deriv (f ∘ g) =ᶠ[𝓝 0] fun t => fderiv ℝ f (g t) v := by
    filter_upwards [ht.eventually (h.eventually (by simp))] with t h'
    exact ((h'.differentiableAt (by decide)).hasFDerivAt.comp_hasDerivAt t (hg t)).deriv
  have hmax : IsLocalMax (f ∘ g) 0 := (he.symm ▸ hm).comp_continuous (hg 0).continuousAt
  have hcont : ContinuousAt (f ∘ g) 0 := (he.symm ▸ h.continuousAt).comp (hg 0).continuousAt
  have hi := deriv_deriv_nonpos_of_localMax hcont hmax
  rw [heq.deriv_eq] at hi
  have hd := (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by decide)
  have hf : HasDerivAt (fun t : ℝ => (fderiv ℝ f (g t)) v)
      ((fderiv ℝ (fderiv ℝ f) x v) v) 0 := by
    have hd' : DifferentiableAt ℝ (fderiv ℝ f) (g 0) := he.symm ▸ hd
    simpa [he] using ((hd'.hasFDerivAt.comp_hasDerivAt 0 (hg 0)).clm_apply (hasDerivAt_const 0 v))
  rw [hf.deriv] at hi
  simpa [iteratedFDeriv_two_apply, v] using hi

private theorem laplacian_radiusSq_real (x : Space n) : Δ (fun z : Space n => ‖z‖ ^ 2) x = 2*n := by
  have he : (fun z : Space n => ‖z‖ ^ 2) = Complex.reCLM ∘ polynomialValue (Polynomial.radiusSq n) := by
    funext z
    simp [polynomialValue_radiusSq, ← Complex.ofReal_pow]
  rw [he, (contDiff_polynomialValue _ 2).contDiffAt.laplacian_CLM_comp_left,
    laplacian_polynomialValue, Polynomial.lap_radiusSq]
  simp [polynomialValue]

theorem harmonic_le_of_frontier (hn : 0 < n) {K : Set (Space n)} (hK : IsCompact K)
    {f : Space n → ℝ} (hc : ContinuousOn f K) (hh : HarmonicOnNhd f (interior K))
    {A : ℝ} (hb : ∀ z ∈ frontier K, f z ≤ A) (x : Space n) (hx : x ∈ K) : f x ≤ A := by
  let r := fun z : Space n => ‖z‖ ^ 2
  have hrad : ContDiff ℝ 2 r := contDiff_norm_sq ℝ
  obtain ⟨M, hM⟩ := hK.bddAbove_image hrad.continuous.continuousOn
  have hpert (ε : ℝ) (hε : 0 < ε) : f x ≤ A + ε*M := by
    let F := f + ε • r
    have hC : ContinuousOn F K := hc.add (continuousOn_const.smul hrad.continuous.continuousOn)
    obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn ⟨x,hx⟩ hC
    have hyb : y ∈ frontier K := by
      refine ⟨subset_closure hy, ?_⟩
      intro hi
      have hloc := hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hi)
      have hhy := hh y hi
      have hc2 : ContDiffAt ℝ 2 (ε • r) y := contDiffAt_const.smul hrad.contDiffAt
      have hNon := laplacian_nonpos_of_localMax (hhy.1.add hc2) hloc
      change Δ (f + ε • r) y ≤ 0 at hNon
      rw [hhy.1.laplacian_add hc2, InnerProductSpace.laplacian_smul ε hrad.contDiffAt,
        hhy.2.self_of_nhds] at hNon
      change 0 + ε * Δ r y ≤ 0 at hNon
      rw [show Δ r y = 2*n from laplacian_radiusSq_real y] at hNon
      have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
      nlinarith [mul_pos hε hn']
    have hxy := hmax hx
    change f x + ε * ‖x‖^2 ≤ f y + ε * ‖y‖^2 at hxy
    have hyM : ‖y‖^2 ≤ M := hM ⟨y,hy,rfl⟩
    nlinarith [hb y hyb, mul_nonneg hε.le (sq_nonneg ‖x‖), mul_le_mul_of_nonneg_left hyM hε.le]
  have ht : Tendsto (fun ε : ℝ => A + ε*M) (𝓝[>] 0) (𝓝 A) := by
    have hc' : Continuous (fun ε : ℝ => A + ε*M) := by fun_prop
    simpa using hc'.continuousAt.continuousWithinAt.tendsto (s := Ioi (0 : ℝ)) (x := 0)
  exact ge_of_tendsto ht (eventually_mem_nhdsWithin.mono fun ε hε => hpert ε hε)

theorem harmonic_norm_le_of_frontier (hn : 0 < n) {K : Set (Space n)} (hK : IsCompact K)
    {u : Space n → ℂ} (hc : ContinuousOn u K) (hh : HarmonicOnNhd u (interior K))
    {A : ℝ} (hb : ∀ z ∈ frontier K, ‖u z‖ ≤ A) (x : Space n) (hx : x ∈ K) : ‖u x‖ ≤ A := by
  obtain ⟨L,hLnorm,hLx⟩ := exists_dual_vector'' ℝ (u x)
  change L (u x) = ‖u x‖ at hLx
  rw [← hLx]
  apply harmonic_le_of_frontier hn hK (L.continuous.comp_continuousOn hc)
    (fun y hy => (hh y hy).comp_CLM L) _ x hx
  intro y hy
  exact (le_abs_self _).trans <| (L.le_opNorm (u y)).trans <|
    (mul_le_mul_of_nonneg_right hLnorm (norm_nonneg _)).trans (by simpa using hb y hy)

end Runcorn
