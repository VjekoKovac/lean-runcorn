module

public import Runcorn.InteriorEstimate
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # From uniform approximation of harmonic functions to L² approximation of gradients -/
@[expose] public section
noncomputable section
open Filter MeasureTheory Set InnerProductSpace Laplacian
open scoped Topology
namespace Runcorn
variable {n : ℕ}
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

private theorem compact_cutoff {K Ω : Set (Space n)} (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ χ : Space n → ℝ, ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      (∀ x, 0 ≤ χ x) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨W,hW,hKW,hKc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  have hN := (hW.inter hΩ).mem_nhdsSet.mpr (subset_inter hKW hKΩ)
  obtain ⟨V,hV,hKV,hVc⟩ := hK.exists_isOpen_closure_subset hN
  obtain ⟨χ,hc,hr,hs,h1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 2) hV hK.isClosed hKV
  have hts : tsupport χ = closure V := by rw [tsupport, hs]
  refine ⟨χ,hc,?_,hts ▸ (hVc.trans inter_subset_right),fun x => (hr ⟨x,rfl⟩).1,fun x hx => (h1 x).mp hx⟩
  change IsCompact (tsupport χ)
  rw [hts]
  exact hKc.of_isClosed_subset isClosed_closure ((hVc.trans inter_subset_left).trans subset_closure)

private theorem complex_energy_bound {K : Set (Space n)} (hK : IsCompact K)
    {χ : Space n → ℝ} (hc : ContDiff ℝ 2 χ) (hk : HasCompactSupport χ)
    (χpos : ∀ x, 0 ≤ χ x) (χone : ∀ x ∈ K, χ x = 1)
    {w : Space n → ℂ} (hw : HarmonicOnNhd w (tsupport χ))
    {ε : ℝ} (hε : ∀ x ∈ tsupport χ, ‖w x‖ ≤ ε) (i : Fin n) :
    (∫ x in K, ‖fderiv ℝ w x (e i)‖ ^ 2) ≤ (∫ x, |Δ χ x|) * ε^2 := by
  let u := Complex.reCLM ∘ w
  let v := Complex.imCLM ∘ w
  have hu := hw.comp_CLM Complex.reCLM
  have hv := hw.comp_CLM Complex.imCLM
  have hR := derivative_sq_integral_le hK hc hk χpos χone hu
    (fun x hx => (Complex.abs_re_le_norm _).trans (hε x hx)) i
  have hI := derivative_sq_integral_le hK hc hk χpos χone hv
    (fun x hx => (Complex.abs_im_le_norm _).trans (hε x hx)) i
  have hKχ : K ⊆ tsupport χ := fun x hx =>
    subset_closure (show χ x ≠ 0 by rw [χone x hx]; exact one_ne_zero)
  have intsq (g : Space n → ℝ) (hg : HarmonicOnNhd g (tsupport χ)) :
      IntegrableOn (fun x => (fderiv ℝ g x (e i)) ^ 2) K := by
    have hcont : ContinuousOn (fun x => (fderiv ℝ g x (e i)) ^ 2) K := fun x hx =>
      ((((hg x (hKχ hx)).1.continuousAt_fderiv (by decide)).clm_apply
        continuousAt_const).pow 2).continuousWithinAt
    exact hcont.integrableOn_compact hK
  have eq : (∫ x in K, ‖fderiv ℝ w x (e i)‖ ^ 2) =
      (∫ x in K, (fderiv ℝ u x (e i)) ^ 2) + (∫ x in K, (fderiv ℝ v x (e i)) ^ 2) := by
    rw [← integral_add (intsq u hu) (intsq v hv)]
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    have hd := ((hw x (hKχ hx)).1.differentiableAt (by decide)).hasFDerivAt
    change ‖fderiv ℝ w x (e i)‖ ^ 2 = _
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [u, v, (Complex.reCLM.hasFDerivAt.comp x hd).fderiv,
      (Complex.imCLM.hasFDerivAt.comp x hd).fderiv, ContinuousLinearMap.comp_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, pow_two]
  rw [eq]
  dsimp [u,v]
  linarith

/-- Uniformly approximate a harmonic function on arbitrary compact subsets
of its open domain by a family of harmonic functions. Then on any chosen
compact set their real coordinate derivatives converge in complex L². -/
theorem exists_gradient_approximants {K Ω : Set (Space n)} (hK : IsCompact K)
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) {u : Space n → ℂ} (hu : HarmonicOnNhd u Ω)
    (M : Set (Space n → ℂ)) (hM : ∀ g ∈ M, HarmonicOnNhd g Ω)
    (ha : ∀ C : Set (Space n), IsCompact C → C ⊆ Ω → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ M, ∀ x ∈ C, ‖g x-u x‖ ≤ ε) :
    ∃ G : ℕ → Space n → ℂ, (∀ j, G j ∈ M) ∧ ∀ i : Fin n,
      Tendsto (fun j => eLpNorm (fun x => fderiv ℝ (G j) x (e i) - fderiv ℝ u x (e i)) 2
        (volume.restrict K)) atTop (𝓝 0) := by
  obtain ⟨χ,hc,hk,hΩχ,hpos,hone⟩ := compact_cutoff hK hΩ hKΩ
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose G hGM hbound using fun j : ℕ => ha (tsupport χ) hk hΩχ (ε j) (by dsimp [ε]; positivity)
  refine ⟨G,hGM,fun i => ?_⟩
  let d (j : ℕ) (x : Space n) := fderiv ℝ (G j) x (e i) - fderiv ℝ u x (e i)
  let A := ∫ x, |Δ χ x|
  have Dbound (j : ℕ) : (∫ x in K, ‖d j x‖^2) ≤ A * ε j ^ 2 := by
    have hG := hM _ (hGM j)
    have hh := (hG.sub hu).mono hΩχ
    have h := complex_energy_bound hK hc hk hpos hone hh (ε := ε j) (hbound j) i
    apply le_trans _ h
    apply le_of_eq
    apply setIntegral_congr_fun hK.measurableSet
    intro x hx
    change ‖d j x‖ ^ 2 = ‖fderiv ℝ (G j - u) x (e i)‖ ^ 2
    rw [fderiv_sub ((hG x (hKΩ hx)).1.differentiableAt (by decide))
      ((hu x (hKΩ hx)).1.differentiableAt (by decide))]
    rfl
  have lim : Tendsto (fun j => ∫ x in K, ‖d j x‖^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => integral_nonneg fun _ => sq_nonneg _) Dbound
    simpa using (tendsto_const_nhds (x := A)).mul (hε.pow 2)
  have hD (j : ℕ) : ContinuousOn (d j) K := by
    intro x hx
    have h1 := ((hu x (hKΩ hx)).1.continuousAt_fderiv (by decide)).clm_apply
      (continuousAt_const (y := e i))
    have h2 := (((hM _ (hGM j)) x (hKΩ hx)).1.continuousAt_fderiv (by decide)).clm_apply
      (continuousAt_const (y := e i))
    exact (h2.sub h1).continuousWithinAt
  have hm (j : ℕ) : MemLp (d j) 2 (volume.restrict K) :=
    (memLp_two_iff_integrable_sq_norm ((hD j).aestronglyMeasurable hK.measurableSet)).mpr
      (((hD j).norm.pow 2).integrableOn_compact hK)
  have eq (j : ℕ) : eLpNorm (d j) 2 (volume.restrict K) =
      ENNReal.ofReal (Real.sqrt (∫ x in K, ‖d j x‖^2)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) (hm j)]
    simp [Real.sqrt_eq_rpow, one_div]
  change Tendsto (fun j => eLpNorm (d j) 2 _) _ _
  simp_rw [eq]
  simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_sqrt.continuousAt.tendsto.comp lim)

end Runcorn
