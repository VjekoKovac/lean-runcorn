module

public import Runcorn.PolynomialCalculus
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! # Polynomial restrictions to the sphere

The angular completeness step of Sections 2 and 3 of arXiv:2607.18379 uses
density on the unit sphere. The uniform polynomial approximation proved here
is the Stone–Weierstrass route to that ingredient. The theorem invoked is the
complex version in mathlib's `Topology.ContinuousMap.StoneWeierstrass`.
-/

@[expose] public section
noncomputable section
open Set MvPolynomial
open scoped ComplexConjugate
namespace Runcorn

/-- Continuous restriction of an ambient polynomial with complex coefficients. -/
def polynomialOnSphere {n : ℕ} (P : MvPolynomial (Fin n) ℂ) : C(Sphere n, ℂ) where
  toFun σ := polynomialValue P σ.val
  continuous_toFun := by
    apply P.continuous_eval.comp
    exact continuous_pi fun i ↦ Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val)

/-- The algebra is closed under conjugation because all the input coordinates
are real. Only the polynomial coefficients have to be conjugated. -/
def spherePolynomialAlgebra (n : ℕ) : StarSubalgebra ℂ C(Sphere n, ℂ) where
  carrier := range (@polynomialOnSphere n)
  one_mem' := ⟨1, by ext σ; simp [polynomialOnSphere, polynomialValue]⟩
  add_mem' := by
    rintro _ _ ⟨P, rfl⟩ ⟨Q, rfl⟩
    exact ⟨P+Q, by ext σ; simp [polynomialOnSphere, polynomialValue]⟩
  zero_mem' := ⟨0, by ext σ; simp [polynomialOnSphere, polynomialValue]⟩
  mul_mem' := by
    rintro _ _ ⟨P, rfl⟩ ⟨Q, rfl⟩
    exact ⟨P*Q, by ext σ; simp [polynomialOnSphere, polynomialValue]⟩
  algebraMap_mem' c := ⟨C c, by ext σ; simp [polynomialOnSphere, polynomialValue]⟩
  star_mem' := by
    rintro _ ⟨P, rfl⟩
    refine ⟨map (starRingEnd ℂ) P, ?_⟩
    ext σ
    change eval (fun i ↦ (σ.val i : ℂ)) (map (starRingEnd ℂ) P) =
      (starRingEnd ℂ) (eval (fun i ↦ (σ.val i : ℂ)) P)
    rw [map_eval]
    simp [Function.comp_def]

/-- Coordinate polynomials separate distinct points on the sphere. -/
theorem spherePolynomialAlgebra_separatesPoints (n : ℕ) :
    (spherePolynomialAlgebra n).SeparatesPoints := by
  intro σ τ hneq
  have h : ∃ i : Fin n, σ.val i ≠ τ.val i := by
    by_contra! hh
    exact hneq (Subtype.ext (PiLp.ext hh))
  obtain ⟨i, hi⟩ := h
  let p := polynomialOnSphere (X i : MvPolynomial (Fin n) ℂ)
  refine ⟨p, ⟨p, ⟨X i, rfl⟩, rfl⟩, ?_⟩
  simpa [p, polynomialOnSphere, polynomialValue] using hi

/-- Every continuous complex function on the unit sphere is a uniform limit
of complex polynomial restrictions to the sphere. -/
theorem denseRange_polynomialOnSphere (n : ℕ) : DenseRange (@polynomialOnSphere n) := by
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (spherePolynomialAlgebra n) (spherePolynomialAlgebra_separatesPoints n)
  intro f
  change f ∈ (spherePolynomialAlgebra n).topologicalClosure
  rw [h]
  trivial


/-- On the sphere, the factor given by the squared radius in the Fischer
decomposition disappears. -/
theorem polynomialValue_radiusSq_sphere {n : ℕ} (σ : Sphere n) :
    polynomialValue (Polynomial.radiusSq n) σ.val = 1 := by
  have hσ : ‖σ.val‖ = 1 := mem_sphere_zero_iff_norm.mp σ.property
  have hnorm := EuclideanSpace.real_norm_sq_eq σ.val
  rw [hσ, one_pow] at hnorm
  simpa [polynomialValue, Polynomial.radiusSq] using
    congrArg (fun t : ℝ ↦ (t : ℂ)) hnorm.symm

/-- A subspace of continuous functions containing every homogeneous harmonic
polynomial restriction contains every polynomial restriction. -/
theorem polynomialOnSphere_mem_of_harmonics {n : ℕ} (hn : 0 < n)
    (W : Submodule ℂ C(Sphere n, ℂ))
    (hW : ∀ (Q : Polynomial.Poly n) (k : ℕ), Q.IsHomogeneous k →
      Polynomial.lap Q = 0 → polynomialOnSphere Q ∈ W)
    (P : Polynomial.Poly n) : polynomialOnSphere P ∈ W := by
  have hhom (Q : Polynomial.Poly n) (d : ℕ) (hQ : Q.IsHomogeneous d) :
      polynomialOnSphere Q ∈ W := by
    obtain ⟨H, hH, he⟩ := Polynomial.exists_fischer hn Q hQ
    have hr : polynomialOnSphere Q = ∑ i ∈ Finset.range (d/2+1), polynomialOnSphere (H i) := by
      ext σ
      have hrad := polynomialValue_radiusSq_sphere σ
      change MvPolynomial.eval _ _ = 1 at hrad
      simp [he, polynomialOnSphere, polynomialValue, hrad]
    rw [hr]
    exact W.sum_mem fun i hi ↦ hW _ _ (hH i (by simpa using hi)).1 (hH i (by simpa using hi)).2
  have hp : polynomialOnSphere P = ∑ d ∈ Finset.range (P.totalDegree + 1),
      polynomialOnSphere (homogeneousComponent d P) := by
    ext σ
    simpa [polynomialOnSphere, polynomialValue] using
      congrArg (MvPolynomial.eval (fun i ↦ (σ.val i : ℂ))) P.sum_homogeneousComponent.symm
  rw [hp]
  exact W.sum_mem fun d _ ↦ hhom _ d (homogeneousComponent_isHomogeneous _ _)

/-- Uniform completeness of all spherical harmonics, formulated independently
of a basis choice. -/
theorem harmonicRestrictions_span_dense {n : ℕ} (hn : 0 < n) :
    (Submodule.span ℂ {Y : C(Sphere n, ℂ) | ∃ k, IsSphericalHarmonic k Y}).topologicalClosure = ⊤ := by
  refine eq_top_iff.mpr (fun f _ ↦ ?_)
  apply closure_mono _ (denseRange_polynomialOnSphere n f)
  rintro _ ⟨P, rfl⟩
  apply polynomialOnSphere_mem_of_harmonics hn
  intro Q k hQ hLap
  exact Submodule.subset_span ⟨k, Q, hQ, harmonic_polynomialValue Q hLap, fun _ ↦ rfl⟩

end Runcorn
