module

public import Runcorn.PolynomialCalculus
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # A local energy estimate for harmonic functions

The identity ∫ χ Δ(h²) = ∫ Δχ h² turns local uniform approximation into
mean-square gradient approximation on smaller shells. The real-valued form
can be applied to both components of a complex-valued harmonic function.
-/
@[expose] public section
noncomputable section
open Filter MeasureTheory Set InnerProductSpace Laplacian
open scoped Topology
namespace Runcorn
variable {n : ℕ}
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

private theorem int_mul_local {u v : Space n → ℝ} (hu : Continuous u)
    (hc : HasCompactSupport u) (hv : ∀ x ∈ tsupport u, ContinuousAt v x) :
    Integrable (fun x => u x * v x) := by
  apply Continuous.integrable_of_hasCompactSupport _ hc.mul_right
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport u
  · exact hu.continuousAt.mul (hv x hx)
  · apply Filter.EventuallyEq.continuousAt (y := 0)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

private theorem local_ibp (i : Fin n) {u v : Space n → ℝ}
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    (hv : ∀ x ∈ tsupport u, ContDiffAt ℝ 1 v x) :
    (∫ x, u x * fderiv ℝ v x (e i)) = -(∫ x, fderiv ℝ u x (e i) * v x) := by
  have hD := (hu.continuous_fderiv (by decide)).clm_apply (continuous_const (y := e i))
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · apply int_mul_local hD (hc.fderiv_apply (𝕜 := ℝ) (e i))
    exact fun x hx => (hv x (tsupport_fderiv_apply_subset ℝ _ hx)).continuousAt
  · apply int_mul_local hu.continuous hc
    exact fun x hx => ((hv x hx).continuousAt_fderiv (by decide)).clm_apply continuousAt_const
  · exact int_mul_local hu.continuous hc fun x hx => (hv x hx).continuousAt
  · exact fun x _ => hu.differentiable (by decide) x
  · exact fun x hx => (hv x hx).differentiableAt (by decide)

private theorem cd_partial {h : Space n → ℝ} {x : Space n} (hc : ContDiffAt ℝ 2 h x)
    (i : Fin n) : ContDiffAt ℝ 1 (fun y => fderiv ℝ h y (e i)) x := by
  exact (hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

/-- Green's identity for a C² cutoff and a function which is C² on a
neighborhood of its support. -/
theorem green_cutoff {χ h : Space n → ℝ} (hc : ContDiff ℝ 2 χ) (hk : HasCompactSupport χ)
    (hh : ∀ x ∈ tsupport χ, ContDiffAt ℝ 2 h x) :
    (∫ x, χ x * Δ h x) = ∫ x, Δ χ x * h x := by
  let D (i : Fin n) (u : Space n → ℝ) := fun x => fderiv ℝ u x (e i)
  have cdχ (i : Fin n) : ContDiff ℝ 1 (D i χ) :=
    contDiff_iff_contDiffAt.mpr fun x => cd_partial hc.contDiffAt i
  have hi (i : Fin n) : (∫ x, χ x * D i (D i h) x) = ∫ x, D i (D i χ) x * h x := by
    rw [local_ibp i (hc.of_le (by norm_num)) hk (fun x hx => cd_partial (hh x hx) i)]
    have h2 := local_ibp (v := h) i (cdχ i) (hk.fderiv_apply (𝕜 := ℝ) (e i))
      (fun x hx => (hh x (tsupport_fderiv_apply_subset ℝ _ hx)).of_le (by norm_num))
    change -(∫ x, D i χ x * D i h x) = _
    change (∫ x, D i χ x * D i h x) = _ at h2
    rw [h2, neg_neg]
  have lint (i : Fin n) : Integrable (fun x => χ x * D i (D i h) x) := by
    apply int_mul_local hc.continuous hk
    exact fun x hx => ((cd_partial (hh x hx) i).continuousAt_fderiv (by decide)).clm_apply
      continuousAt_const
  have rint (i : Fin n) : Integrable (fun x => D i (D i χ) x * h x) := by
    apply int_mul_local (((cdχ i).continuous_fderiv (by decide)).clm_apply continuous_const)
      ((hk.fderiv_apply (𝕜 := ℝ) (e i)).fderiv_apply (𝕜 := ℝ) (e i))
    exact fun x hx => (hh x (tsupport_fderiv_apply_subset ℝ _ (tsupport_fderiv_apply_subset ℝ _ hx))).continuousAt
  calc
    _ = ∫ x, ∑ i, χ x * D i (D i h) x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← Finset.mul_sum]
      by_cases hx : x ∈ tsupport χ
      · rw [laplacian_eq_sum_partials (hh x hx)]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    _ = _ := by
      rw [integral_finsetSum _ fun i _ => lint i]
      simp_rw [hi]
      rw [← integral_finsetSum _ fun i _ => rint i]
      apply integral_congr_ae
      filter_upwards with x
      rw [← Finset.sum_mul, laplacian_eq_sum_partials hc.contDiffAt]

/-- The Laplacian of the square of a real harmonic function equals twice
the squared Euclidean gradient norm. -/
theorem laplacian_sq_harmonic {h : Space n → ℝ} {x : Space n} (hh : HarmonicAt h x) :
    Δ (fun y => h y ^ 2) x = 2 * ∑ i, (fderiv ℝ h x (e i)) ^ 2 := by
  let D (i : Fin n) (g : Space n → ℝ) := fun y => fderiv ℝ g y (e i)
  have hd := hh.1.differentiableAt (by decide)
  have calcD (i : Fin n) : D i (fun y => h y ^ 2) =ᶠ[𝓝 x] fun y => 2 * (h y * D i h y) := by
    filter_upwards [hh.eventually] with y hy
    dsimp only [D]
    rw [((hy.1.differentiableAt (by decide)).hasFDerivAt.pow 2).fderiv]
    simp [nsmul_eq_mul, mul_assoc]
  have second (i : Fin n) : D i (D i (fun y => h y ^ 2)) x =
      2 * (D i h x ^ 2 + h x * D i (D i h) x) := by
    have hd' := (cd_partial hh.1 i).differentiableAt (by decide)
    change fderiv ℝ (D i (fun y => h y ^ 2)) x _ = _
    have hm : DifferentiableAt ℝ (fun y => h y * D i h y) x := hd.mul hd'
    rw [(calcD i).fderiv_eq, fderiv_const_mul hm 2,
      fderiv_fun_mul hd hd']
    simp only [smul_apply, smul_eq_mul, add_apply, D]
    ring
  rw [laplacian_eq_sum_partials (hh.1.pow 2)]
  change (∑ i, D i (D i (fun y => h y ^ 2)) x) = _
  simp_rw [second, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hzero : (∑ i, D i (D i h) x) = 0 :=
    (laplacian_eq_sum_partials hh.1).symm.trans hh.2.self_of_nhds
  simp [hzero, D]

/-- A harmonic error on a neighborhood of a compactly supported cutoff
satisfies the exact local energy identity. -/
theorem local_energy_harmonic {χ h : Space n → ℝ} (hc : ContDiff ℝ 2 χ)
    (hk : HasCompactSupport χ) (hh : HarmonicOnNhd h (tsupport χ)) :
    (∫ x, χ x * (∑ i, (fderiv ℝ h x (e i))^2)) =
      (∫ x, Δ χ x * h x ^ 2) / 2 := by
  have hg := green_cutoff hc hk (h := fun x => h x ^ 2) fun x hx => (hh x hx).1.pow _
  have he : (fun x => χ x * Δ (fun y => h y ^ 2) x) =
      (fun x => 2 * (χ x * ∑ i, (fderiv ℝ h x (e i))^2)) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · rw [laplacian_sq_harmonic (hh x hx)]; ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [he, integral_const_mul] at hg
  linarith

/-- A compactly supported C² cutoff has integrable Laplacian. -/
theorem cutoff_laplacian_integrable {χ : Space n → ℝ} (hc : ContDiff ℝ 2 χ)
    (hk : HasCompactSupport χ) : Integrable (Δ χ) := by
  have he : Δ χ = fun x => ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ χ y (e i)) x (e i) :=
    funext fun _ => laplacian_eq_sum_partials hc.contDiffAt
  rw [he]
  apply integrable_finsetSum
  intro i _
  have h1 : ContDiff ℝ 1 (fun y => fderiv ℝ χ y (e i)) :=
    contDiff_iff_contDiffAt.mpr fun _ => cd_partial hc.contDiffAt i
  exact ((h1.continuous_fderiv (by decide)).clm_apply continuous_const).integrable_of_hasCompactSupport
    ((hk.fderiv_apply (𝕜 := ℝ) (e i)).fderiv_apply (𝕜 := ℝ) (e i))

/-- Mean-square control of one coordinate derivative by the squared uniform
error on the support of a cutoff equal to one on K. -/
theorem derivative_sq_integral_le {χ h : Space n → ℝ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : ContDiff ℝ 2 χ) (hk : HasCompactSupport χ)
    (χpos : ∀ x, 0 ≤ χ x) (h1 : ∀ x ∈ K, χ x = 1)
    (hh : HarmonicOnNhd h (tsupport χ)) {ε : ℝ} (hε : ∀ x ∈ tsupport χ, |h x| ≤ ε)
    (i : Fin n) :
    (∫ x in K, (fderiv ℝ h x (e i))^2) ≤ (∫ x, |Δ χ x|) * ε^2 / 2 := by
  let D := fun (j : Fin n) (x : Space n) => fderiv ℝ h x (e j)
  have hsub : K ⊆ tsupport χ := fun x hx =>
    subset_closure (show χ x ≠ 0 by rw [h1 x hx]; exact one_ne_zero)
  have hder (j : Fin n) (x : Space n) (hx : x ∈ tsupport χ) : ContinuousAt (D j) x :=
    ((hh x hx).1.continuousAt_fderiv (by decide)).clm_apply continuousAt_const
  have hsum (x : Space n) (hx : x ∈ tsupport χ) :
      ContinuousAt (fun y => ∑ j, (D j y)^2) x :=
    tendsto_finsetSum _ fun j _ => (hder j x hx).pow 2
  have hI : Integrable (fun x => χ x * ∑ j, (D j x)^2) :=
    int_mul_local hc.continuous hk hsum
  have hzero (x : Space n) (hx : x ∉ tsupport χ) : Δ χ x = 0 := by
    have eq0 := notMem_tsupport_iff_eventuallyEq.mp hx
    exact (laplacian_congr_nhds eq0).self_of_nhds.trans (show Δ (fun _ : Space n => (0:ℝ)) x = 0 by simp)
  have hJI : Integrable (fun x => Δ χ x * h x ^ 2) := by
    have hx2 : ∀ x ∈ tsupport χ, ContinuousAt (fun y => h y ^ 2) x :=
      fun x hx => (hh x hx).1.continuousAt.pow 2
    have he : Δ χ = fun x => ∑ j : Fin n, fderiv ℝ (fun y => fderiv ℝ χ y (e j)) x (e j) :=
      funext fun _ => laplacian_eq_sum_partials hc.contDiffAt
    simp_rw [he, Finset.sum_mul]
    apply integrable_finsetSum
    intro j _
    have hd : ContDiff ℝ 1 (fun y => fderiv ℝ χ y (e j)) :=
      contDiff_iff_contDiffAt.mpr fun _ => cd_partial hc.contDiffAt j
    apply int_mul_local ((hd.continuous_fderiv (by decide)).clm_apply continuous_const)
      ((hk.fderiv_apply (𝕜 := ℝ) (e j)).fderiv_apply (𝕜 := ℝ) (e j))
    exact fun x hx => hx2 x (tsupport_fderiv_apply_subset ℝ _ (tsupport_fderiv_apply_subset ℝ _ hx))
  calc
    _ ≤ ∫ x in K, χ x * ∑ j, (D j x)^2 := by
      apply setIntegral_mono_on _ hI.integrableOn hK.measurableSet
      · intro x hx
        rw [h1 x hx, one_mul]
        exact Finset.single_le_sum (f := fun j => (D j x)^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      · exact (show ContinuousOn (fun x => (D i x)^2) K from fun x hx =>
          ((hder i x (hsub hx)).pow 2).continuousWithinAt).integrableOn_compact hK
    _ ≤ ∫ x, χ x * ∑ j, (D j x)^2 := setIntegral_le_integral hI
      (ae_of_all _ fun x => mul_nonneg (χpos x) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = _ := local_energy_harmonic hc hk hh
    _ ≤ _ := by
      rw [← integral_mul_const]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply integral_mono hJI ((cutoff_laplacian_integrable hc hk).abs.mul_const _)
      intro x
      by_cases hx : x ∈ tsupport χ
      · exact (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (sq_le_sq' (neg_le.mp ((neg_le_abs _).trans (hε x hx))) ((le_abs_self _).trans (hε x hx))) (abs_nonneg _))
      · simp [hzero x hx]

end Runcorn
