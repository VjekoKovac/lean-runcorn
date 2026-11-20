module

public import Runcorn.Kelvin
public import Runcorn.MaximumPrinciple
public import Runcorn.TestRegularity
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The exterior maximum principle in the plane
A logarithmic barrier bounds a bounded harmonic function by its values on
the inner circle. This allows a finite exterior approximation to have a
constant mode, whose derivative is zero.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Metric Set InnerProductSpace MvPolynomial Laplacian
open scoped Topology
namespace Runcorn

private def logRadius (x : Space 2) : ℂ := ↑(Real.log ‖x‖)
local notation "e" => fun i : Fin 2 => EuclideanSpace.single i (1 : ℝ)

private theorem logRadius_partial {x : Space 2} (hx : x ≠ 0) (i : Fin 2) :
    fderiv ℝ logRadius x (e i) = weightedPoly (-2) (X i) x := by
  have h0 := norm_ne_zero_iff.mpr hx
  have hnorm : HasFDerivAt (fun y : Space 2 => ‖y‖)
      ((1 / (2 * ‖x‖)) • (2 • innerSL ℝ x)) x := by
    simpa using (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 h0)
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x (hnorm.log h0)
  change fderiv ℝ (Complex.ofRealCLM ∘ fun z : Space 2 => Real.log ‖z‖) x (e i) = _
  rw [hd.fderiv]
  simp [weightedPoly, polynomialValue, innerSL_apply_apply, EuclideanSpace.inner_single_right]
  field_simp

private theorem harmonicAt_logRadius {x : Space 2} (hx : x ≠ 0) :
    HarmonicAt logRadius x := by
  have hcd (z : Space 2) (hz : z ≠ 0) : ContDiffAt ℝ 2 logRadius z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z ((contDiffAt_norm ℝ hz).log (norm_ne_zero_iff.mpr hz))
  refine ⟨hcd _ hx, ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  rw [laplacian_eq_sum_partials (hcd y hy)]
  have hh (i : Fin 2) :
      (fun z => fderiv ℝ logRadius z (e i)) =ᶠ[𝓝 y] weightedPoly (-2) (X i) :=
    (eventually_ne_nhds hy).mono fun _ hz => logRadius_partial hz i
  have he (i : Fin 2) : fderiv ℝ (fun z => fderiv ℝ logRadius z (e i)) y (e i) =
      weightedPoly (-2) (pderiv i (X i)) y +
      (-2 : ℂ) * weightedPoly (-4) (X i * X i) y := by
    rw [(hh i).fderiv_eq]
    convert weightedPoly_partial (-2) (X i) i hy using 1
    norm_num
  simp_rw [he]
  have hnorm : ((y 0 : ℂ)^2 + (y 1 : ℂ)^2) = (‖y‖ : ℂ)^2 := by
    have h := EuclideanSpace.real_norm_sq_eq y
    rw [Fin.sum_univ_two] at h
    exact_mod_cast h.symm
  simp only [Fin.sum_univ_two, weightedPoly, pderiv_X_self, polynomialValue, map_mul,
    map_one, eval_X, mul_one]
  norm_num
  field_simp [norm_ne_zero_iff.mpr hy]
  linear_combination (norm := ring_nf) -2 * hnorm

theorem harmonicAt_planar_log_norm {x : Space 2} (hx : x ≠ 0) :
    HarmonicAt (fun z : Space 2 => Real.log ‖z‖) x := by
  exact (harmonicAt_logRadius hx).comp_CLM Complex.reCLM

/-- Exterior maximum principle for bounded complex harmonic functions in the
plane. No decay assumption is needed. -/
theorem planar_exterior_norm_le {c A M : ℝ} (hc : 0 < c) {w : Space 2 → ℂ}
    (hwc : ContinuousOn w {x | c ≤ ‖x‖}) (hw : HarmonicOnNhd w {x | c < ‖x‖})
    (hb : ∀ x : Space 2, c ≤ ‖x‖ → ‖w x‖ ≤ M)
    (hbdy : ∀ x : Space 2, ‖x‖ = c → ‖w x‖ ≤ A)
    (x : Space 2) (hx : c ≤ ‖x‖) : ‖w x‖ ≤ A := by
  obtain ⟨L, hLn, hLx⟩ := exists_dual_vector'' ℝ (w x)
  let f := fun y => L (w y)
  have hf (y : Space 2) : f y ≤ ‖w y‖ :=
    (le_abs_self _).trans <| (L.le_opNorm _).trans <| by
      simpa using mul_le_mul_of_nonneg_right hLn (norm_nonneg (w y))
  have hpert (ε : ℝ) (hε : 0 < ε) : f x ≤ A + ε * (Real.log ‖x‖ - Real.log c) := by
    let R := max ‖x‖ (Real.exp ((M-A)/ε + Real.log c))
    have hR : ‖x‖ ≤ R := le_max_left _ _
    have hlog : (M-A)/ε + Real.log c ≤ Real.log R := by
      rw [← Real.log_exp ((M-A)/ε + Real.log c)]
      exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
    let u := fun y : Space 2 => f y - ε * (Real.log ‖y‖ - Real.log c)
    have hu {y : Space 2} (hy : c < ‖y‖) : HarmonicAt u y := by
      exact ((hw y hy).comp_CLM L).sub (((harmonicAt_planar_log_norm
        (norm_pos_iff.mp (hc.trans hy))).sub (harmonicAt_const (Real.log c))).const_smul (c := ε))
    have hbase : HarmonicOnNhd u (interior (annulus c R)) := by
      intro y hy
      have hsub : annulus (n:=2) c R ⊆ (ball (0 : Space 2) c)ᶜ := by
        intro z hz
        simpa using (not_lt.mpr hz.1)
      have hi := interior_mono hsub hy
      rw [interior_compl, closure_ball (0 : Space 2) hc.ne'] at hi
      apply hu
      simpa using hi
    have huc : ContinuousOn u (annulus c R) := by
      apply (L.continuous.comp_continuousOn (hwc.mono fun z hz => hz.1)).sub
      apply continuousOn_const.mul
      apply ContinuousOn.sub _ continuousOn_const
      exact continuous_norm.continuousOn.log fun z hz => (hc.trans_le hz.1).ne' 
    have hbound (y : Space 2) (hy : y ∈ frontier (annulus c R)) : u y ≤ A := by
      have hmem := continuous_norm.frontier_preimage_subset (Icc c R) hy
      rw [frontier_Icc (hx.trans hR)] at hmem
      change ‖y‖ ∈ ({c, R} : Set ℝ) at hmem
      rcases hmem with hyc | hyR
      · simpa [u, hyc] using (hf y).trans (hbdy y hyc)
      · have hey : ‖y‖ = R := hyR
        have hM : f y ≤ M := (hf y).trans (hb y (hey ▸ hx.trans hR))
        have houter : M-A ≤ ε*(Real.log R - Real.log c) := by
          have hh := (div_le_iff₀ hε).mp (show (M-A)/ε ≤ Real.log R - Real.log c by linarith)
          linarith [mul_comm (Real.log R - Real.log c) ε]
        dsimp [u]
        rw [hey]
        linarith
    have hmax := harmonic_le_of_frontier (by norm_num : 0 < 2) (isCompact_annulus c R)
      huc hbase hbound x ⟨hx,hR⟩
    dsimp [u] at hmax
    linarith
  have he : f x = ‖w x‖ := by simpa [f] using hLx
  rw [← he]
  have ht : Tendsto (fun ε : ℝ => A + ε * (Real.log ‖x‖ - Real.log c))
      (𝓝[>] 0) (𝓝 A) := by
    have hcont : Continuous (fun ε : ℝ => A + ε * (Real.log ‖x‖ - Real.log c)) := by fun_prop
    simpa [ContinuousWithinAt] using hcont.continuousAt.continuousWithinAt
      (x := (0 : ℝ)) (s := Ioi (0 : ℝ))
  exact ge_of_tendsto ht (eventually_mem_nhdsWithin.mono fun ε hε => hpert ε hε)

end Runcorn
