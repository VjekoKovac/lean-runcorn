module

public import Runcorn.SphereDensity
public import Runcorn.Series
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Angular completeness for the basis of Theorem 2

The uniform Stone–Weierstrass/Fischer conclusion transfers to the specified
orthogonal family in surface L². The density of continuous functions in L²
of a finite Borel measure is mathlib's `ContinuousMap.toLp_denseRange`.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace Runcorn

private def basisContinuousMap {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (a : Mode n) : C(Sphere n, ℂ) where
  toFun := Y a.1 a.2
  continuous_toFun := by
    obtain ⟨P, _, _, hp⟩ := (hY a.1).1 a.2
    have he : Y a.1 a.2 = polynomialOnSphere P := funext hp
    rw [he]
    exact (polynomialOnSphere P).continuous

/-- Finite linear combinations of the supplied basis elements, across all degrees,
are uniformly dense. -/
private theorem angularBasis_uniform_span_dense {n : ℕ} (hn : 0 < n)
    (Y : AngularFamily n) (hY : IsAngularBasis Y) :
    (Submodule.span ℂ (range (basisContinuousMap Y hY))).topologicalClosure = ⊤ := by
  refine top_unique ?_
  rw [← harmonicRestrictions_span_dense hn]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro Z ⟨k, hk⟩
  obtain ⟨c, hc⟩ := (hY k).2.2.1 Z hk
  have he : Z = ∑ j, c j • basisContinuousMap Y hY ⟨k,j⟩ := by
    ext σ
    simpa [basisContinuousMap, smul_eq_mul] using hc σ
  rw [he]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k,j⟩, rfl⟩)

/-- Completeness of the angular L² vectors, for an arbitrary unnormalized
orthogonal basis in each degree, exactly as selected in the paper. -/
theorem angularBasis_span_dense {n : ℕ} (hn : 0 < n) (Y : AngularFamily n)
    (hY : IsAngularBasis Y) :
    (Submodule.span ℂ (range (angularVector Y hY))).topologicalClosure = ⊤ := by
  let μ := surfaceMeasure n
  let : IsFiniteMeasure μ := by dsimp [μ, surfaceMeasure]; infer_instance
  let T : C(Sphere n, ℂ) →L[ℂ] AngularL2 n := ContinuousMap.toLp 2 μ ℂ
  have hd : DenseRange T := ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num)
  have hmap (a : Mode n) : T (basisContinuousMap Y hY a) = angularVector Y hY a := by
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp μ (basisContinuousMap Y hY a)).trans
      (angularVector_coe_ae Y hY a).symm
  have hu := hd.topologicalClosure_map_submodule (angularBasis_uniform_span_dense hn Y hY)
  rw [Submodule.map_span] at hu
  have he : range (angularVector Y hY) = (T : C(Sphere n, ℂ) → AngularL2 n) '' range (basisContinuousMap Y hY) := by
    ext f
    change (∃ a, angularVector Y hY a = f) ↔ _
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨basisContinuousMap Y hY a, ⟨a,rfl⟩, hmap a⟩
    · rintro ⟨_, ⟨a,rfl⟩, rfl⟩
      exact ⟨a, (hmap a).symm⟩
  simpa only [he, ContinuousLinearMap.coe_coe] using hu


end Runcorn
