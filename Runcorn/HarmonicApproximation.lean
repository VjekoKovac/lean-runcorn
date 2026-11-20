module

public import Runcorn.MaximumPrinciple
public import Runcorn.ExteriorAsymptotics
public import Runcorn.PlanarExterior

/-! # Uniform approximation on compact balls by finite sums of solid harmonics

Approximate the trace of the function on a sphere by spherical harmonics.
The weak maximum principle bounds the error throughout the enclosed ball.
-/
@[expose] public section
noncomputable section
open Set Metric InnerProductSpace Filter Topology
namespace Runcorn

/-- Normalize a point of a sphere of positive radius to the unit sphere. -/
theorem exists_sphere_direction {n : ℕ} {r : ℝ} (hr : 0 < r) {x : Space n}
    (hx : ‖x‖ = r) : ∃ σ : Sphere n, x = r • σ.val := by
  refine ⟨⟨r⁻¹ • x, mem_sphere_zero_iff_norm.mpr ?_⟩, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hx, inv_mul_cancel₀ hr.ne']
  · change x = r • (r⁻¹ • x)
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

/-- On any smaller closed ball, a harmonic function is uniformly approximated
by finite sums of its admissible interior mode types. -/
theorem approximate_interior_on_ball {n : ℕ} (hn : 0 < n) {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    {u : Space n → ℂ} (hu : HarmonicOnNhd u {x | ‖x‖ < R}) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ interiorModeSpan n, ∀ x ∈ closedBall (0 : Space n) r, ‖u x - U x‖ ≤ ε := by
  let F : C(Sphere n, ℂ) := ⟨fun σ => u (r • σ.val), by
    refine hu.continuousOn.comp_continuous (by fun_prop) ?_
    intro σ
    change ‖r • σ.val‖ < R
    rwa [norm_polarPoint_of_sphere r hr σ]⟩
  obtain ⟨U,hU,hs⟩ := approximate_interior_trace hn hr F hε
  refine ⟨U, hU, ?_⟩
  have hball : closedBall (0 : Space n) r ⊆ {x | ‖x‖ < R} := by
    intro x hx
    exact (mem_closedBall_zero_iff.mp hx).trans_lt hrR
  have hh := (hu.mono hball).sub ((interiorModeSpan_harmonic hU).mono (subset_univ _))
  apply harmonic_norm_le_of_frontier hn (isCompact_closedBall (0 : Space n) r) hh.continuousOn
    (hh.mono interior_subset)
  intro x hx
  obtain ⟨σ,rfl⟩ := exists_sphere_direction hr
    (mem_sphere_zero_iff_norm.mp (frontier_closedBall_subset_sphere hx))
  exact (hs σ).le


private theorem bound_on_exterior {n : ℕ} {r : ℝ} {w : Space n → ℂ}
    (hc : ContinuousOn w {x | r ≤ ‖x‖}) {c : ℂ}
    (ht : Tendsto w (comap (fun x : Space n => ‖x‖) atTop) (𝓝 c)) :
    ∃ B : ℝ, ∀ x : Space n, r ≤ ‖x‖ → ‖w x‖ ≤ B := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp (eventually_comap.mp (Metric.tendsto_nhds.mp ht 1 zero_lt_one))
  obtain ⟨M,hM⟩ := (isCompact_annulus (n := n) r R).bddAbove_image (hc.norm.mono fun _ hx => hx.1)
  refine ⟨max M (1 + ‖c‖), fun x hx => ?_⟩
  by_cases h : ‖x‖ ≤ R
  · exact (hM ⟨x, ⟨hx,h⟩,rfl⟩).trans (le_max_left _ _)
  · calc
      ‖w x‖ = dist (w x) 0 := (dist_zero_right _).symm
      _ ≤ dist (w x) c + dist c 0 := dist_triangle _ _ _
      _ ≤ 1 + ‖c‖ := by rw [dist_zero_right]; gcongr; exact (hR _ (le_of_not_ge h) x rfl).le
      _ ≤ _ := le_max_right _ _

/-- Boundary data on one sphere control exterior approximations in every
dimension. In the plane a bounded difference is controlled using the
logarithmic barrier; in higher dimensions both fields decay. -/
theorem approximate_exterior {n : ℕ} (hn : 2 ≤ n) {lo r : ℝ} (hlo : 0 < lo) (hr : lo < r)
    {v : Space n → ℂ} (hv : HarmonicOnNhd v {x | lo < ‖x‖})
    (hlim : Tendsto v (comap (fun x : Space n => ‖x‖) atTop) (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ exteriorModeSpan n, ∀ x : Space n, r ≤ ‖x‖ → ‖v x - V x‖ ≤ ε := by
  have hr0 := hlo.trans hr
  let F : C(Sphere n, ℂ) := ⟨fun σ => v (r • σ.val), by
    apply hv.continuousOn.comp_continuous (by fun_prop)
    intro σ
    change lo < ‖r • σ.val‖
    rwa [norm_polarPoint_of_sphere r hr0 σ]⟩
  obtain ⟨V,hV,hs⟩ := approximate_exterior_trace (by omega) hr0 F hε
  refine ⟨V,hV,?_⟩
  let w := v - V
  have hh : HarmonicOnNhd w {x | r ≤ ‖x‖} :=
    (hv.mono (fun x h => hr.trans_le h)).sub
      ((exteriorModeSpan_harmonic hV).mono (fun x h => norm_pos_iff.mp (hr0.trans_le h)))
  have hbdy (x : Space n) (hx : ‖x‖ = r) : ‖w x‖ ≤ ε := by
    obtain ⟨σ,rfl⟩ := exists_sphere_direction hr0 hx
    exact (hs σ).le
  obtain ⟨c,hc,hend⟩ := exteriorModeSpan_limit hn hV
  have hwend : Tendsto w (comap (fun x : Space n => ‖x‖) atTop) (𝓝 (0-c)) := hlim.sub hend
  by_cases hn2 : n = 2
  · subst n
    obtain ⟨B,hB⟩ := bound_on_exterior hh.continuousOn hwend
    exact planar_exterior_norm_le hr0 hh.continuousOn (hh.mono (fun x (h : r < ‖x‖) => (show r ≤ ‖x‖ from h.le))) hB hbdy
  · rw [hc (by omega), sub_zero] at hwend
    obtain ⟨R,hR⟩ := eventually_atTop.mp (eventually_comap.mp (Metric.tendsto_nhds.mp hwend ε hε))
    intro x hx
    let T := max R ‖x‖
    have hxT : ‖x‖ ≤ T := le_max_right _ _
    have hh' := hh.mono (show annulus r T ⊆ _ from fun _ h => h.1)
    apply harmonic_norm_le_of_frontier (by omega) (isCompact_annulus r T) hh'.continuousOn
      (hh'.mono interior_subset) _ x ⟨hx,hxT⟩
    intro y hy
    have hf := continuous_norm.frontier_preimage_subset (Icc r T) hy
    rw [frontier_Icc (hx.trans hxT)] at hf
    change ‖y‖ ∈ ({r, T} : Set ℝ) at hf
    rcases hf with hy | hy
    · exact hbdy y hy
    · have he : ‖y‖ = T := hy
      simpa only [dist_zero_right] using (hR T (le_max_left _ _) y he).le

/-- Uniform approximation on any compact subset of the interior domain. -/
theorem approximate_interior_on_compact {n : ℕ} (hn : 0 < n) {R : ℝ} (_hR : 0 < R)
    {u : Space n → ℂ} (hu : HarmonicOnNhd u {x | ‖x‖ < R}) (K : Set (Space n))
    (hK : IsCompact K) (hsub : K ⊆ {x | ‖x‖ < R}) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ interiorModeSpan n, ∀ x ∈ K, ‖U x - u x‖ ≤ ε := by
  rcases K.eq_empty_or_nonempty with rfl | hnK
  · exact ⟨0, (interiorModeSpan n).zero_mem, by simp⟩
  obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn hnK continuous_norm.continuousOn
  obtain ⟨r,hyr,hrR⟩ := exists_between (hsub hy : ‖y‖ < R)
  obtain ⟨U,hU,he⟩ := approximate_interior_on_ball hn ((norm_nonneg _).trans_lt hyr) hrR hu hε
  refine ⟨U,hU,fun x hx => ?_⟩
  rw [norm_sub_rev]
  exact he x (mem_closedBall_zero_iff.mpr ((hmax hx).trans hyr.le))

/-- Uniform approximation on any compact subset of the exterior domain. -/
theorem approximate_exterior_on_compact {n : ℕ} (hn : 2 ≤ n) {lo : ℝ} (hlo : 0 < lo)
    {v : Space n → ℂ} (hv : HarmonicOnNhd v {x | lo < ‖x‖})
    (hlim : Tendsto v (comap (fun x : Space n => ‖x‖) atTop) (𝓝 0))
    (K : Set (Space n)) (hK : IsCompact K) (hsub : K ⊆ {x | lo < ‖x‖})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ exteriorModeSpan n, ∀ x ∈ K, ‖V x - v x‖ ≤ ε := by
  rcases K.eq_empty_or_nonempty with rfl | hnK
  · exact ⟨0, (exteriorModeSpan n).zero_mem, by simp⟩
  obtain ⟨y,hy,hmin⟩ := hK.exists_isMinOn hnK continuous_norm.continuousOn
  obtain ⟨V,hV,he⟩ := approximate_exterior hn hlo (hsub hy) hv hlim hε
  refine ⟨V,hV,fun x hx => ?_⟩
  rw [norm_sub_rev]
  exact he x (hmin hx)

end Runcorn
