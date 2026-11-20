module

public import Runcorn.SphereDensity
public import Runcorn.LowModes
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.MeasureTheory.Function.L2Space

/-! # The basis-free low-degree projection used for varying radii -/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate InnerProductSpace
namespace Runcorn

/-- Restrictions of all spherical harmonics of degrees strictly below d,
and all of their finite linear combinations. -/
def lowAngularSpan (n d : ℕ) : Submodule ℂ C(Sphere n, ℂ) :=
  Submodule.span ℂ {Y : C(Sphere n,ℂ) | ∃ k < d, IsSphericalHarmonic k Y}

private theorem lowAngularSpan_finite (n d : ℕ) (hd : d ≤ 2) :
    FiniteDimensional ℂ (lowAngularSpan n d) := by
  let L : Fin n → C(Sphere n, ℂ) := fun i ↦ polynomialOnSphere (MvPolynomial.X i)
  let S : Set C(Sphere n, ℂ) := insert (1 : C(Sphere n,ℂ)) (range L)
  let W := Submodule.span ℂ S
  let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ ((finite_range L).insert _)
  apply Submodule.finiteDimensional_of_le (S₂ := W)
  refine Submodule.span_le.mpr ?_
  rintro Z ⟨k,hk,hZ⟩
  have hw1 : (1 : C(Sphere n, ℂ)) ∈ W := Submodule.subset_span (mem_insert _ _)
  have hwL (i : Fin n) : L i ∈ W := Submodule.subset_span (mem_insert_of_mem _ ⟨i,rfl⟩)
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · obtain ⟨c, hc⟩ := degree_zero_is_constant hZ
    have he : Z = c • (1 : C(Sphere n, ℂ)) := by ext σ; simpa using hc σ
    rw [he]
    exact W.smul_mem _ hw1
  · obtain ⟨c, hc⟩ := degree_one_is_linear hZ
    have he : Z = ∑ i, c i • L i := by
      ext σ
      simpa [L, smul_eq_mul, polynomialOnSphere, polynomialValue] using hc σ
    rw [he]
    exact W.sum_mem fun i _ ↦ W.smul_mem _ (hwL i)

/-- Orthogonal projection to degrees below d. Completeness is supplied by the
proved uniform approximation result. Orthogonality between distinct degrees is
isolated in hcross. No angular basis is chosen. -/
theorem mem_lowAngularSpan_of_high_moments {n d : ℕ} (hn : 0 < n) (hd : d ≤ 2)
    (F : C(Sphere n, ℂ))
    (hcross : ∀ (p q : ℕ) (Y Z : C(Sphere n, ℂ)), p ≠ q →
      IsSphericalHarmonic p Y → IsSphericalHarmonic q Z →
      (∫ σ, Z σ * conj (Y σ) ∂surfaceMeasure n) = 0)
    (hf : ∀ (k : ℕ) (Y : C(Sphere n, ℂ)), d ≤ k → IsSphericalHarmonic k Y →
      (∫ σ, F σ * conj (Y σ) ∂surfaceMeasure n) = 0) : F ∈ lowAngularSpan n d := by
  let μ := surfaceMeasure n
  let : IsFiniteMeasure μ := by dsimp [μ, surfaceMeasure]; infer_instance
  let : μ.IsOpenPosMeasure := by dsimp [μ, surfaceMeasure]; infer_instance
  let T : C(Sphere n, ℂ) →L[ℂ] Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ
  let W := lowAngularSpan n d
  let : FiniteDimensional ℂ W := lowAngularSpan_finite n d hd
  let U := W.map T.toLinearMap
  let : FiniteDimensional ℂ U := inferInstanceAs (FiniteDimensional ℂ (W.map T.toLinearMap))
  let P := U.orthogonalProjectionOnto (T F)
  obtain ⟨G, hG, hg⟩ := P.property
  change T G = P.val at hg
  let R := T F - T G
  have hlow : R ∈ Uᗮ := by
    change T F - T G ∈ Uᗮ
    rw [hg]
    exact U.sub_starProjection_mem_orthogonal _
  have hzero (k : ℕ) (Y : C(Sphere n,ℂ)) (hY : IsSphericalHarmonic k Y) :
      inner ℂ (T Y) R = 0 := by
    by_cases hkd : k < d
    · exact hlow _ ⟨Y, Submodule.subset_span ⟨k,hkd,hY⟩, rfl⟩
    · have hG' : inner ℂ (T Y) (T G) = 0 := by
        apply Submodule.span_induction (s := {Z : C(Sphere n,ℂ) | ∃ p < d, IsSphericalHarmonic p Z})
          (p := fun Z _ ↦ inner ℂ (T Y) (T Z) = 0) ?_ ?_ ?_ ?_ hG
        · rintro Z ⟨p,hpd,hZ⟩
          rw [show inner ℂ (T Y) (T Z) = _ from ContinuousMap.inner_toLp μ Y Z]
          exact hcross k p Y Z (by omega) hY hZ
        · simp
        · intro x y _ _ hx hy
          simp [map_add, inner_add_right, hx, hy]
        · intro a x _ hx
          simp [map_smul, inner_smul_right, hx]
      rw [show R = T F - T G from rfl, inner_sub_right, hG', sub_zero]
      exact (ContinuousMap.inner_toLp μ Y F).trans (hf k Y (by omega) hY)
  let K := (ℂ ∙ R)ᗮ
  have hmem (f : C(Sphere n,ℂ)) : T f ∈ K := by
    let S := K.comap T.toLinearMap
    have hS : IsClosed (S : Set C(Sphere n, ℂ)) := (ℂ ∙ R).isClosed_orthogonal.preimage T.continuous
    have hle : Submodule.span ℂ {Y : C(Sphere n,ℂ) | ∃ k, IsSphericalHarmonic k Y} ≤ S := by
      apply Submodule.span_le.mpr
      rintro Y ⟨k,hY⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (hzero k Y hY)
    have htop := Submodule.topologicalClosure_minimal _ hle hS
    rw [harmonicRestrictions_span_dense hn] at htop
    exact htop (Submodule.mem_top : f ∈ ⊤)
  have hself := Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hmem (F-G))
  rw [map_sub] at hself
  have hz : T F = T G := sub_eq_zero.mp (inner_self_eq_zero.mp hself)
  have he : F = G := ContinuousMap.toLp_injective μ hz
  exact he ▸ hG

end Runcorn
