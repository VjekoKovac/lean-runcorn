module

public import Runcorn.Expansion
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Fourier series in the angular variable

This section isolates the Hilbert-space step of the fixed-annulus proof. The
final theorem takes the density and the cross-degree orthogonality properties
of spherical harmonics as explicit hypotheses. Its complex coefficients have
the numerator and denominator of equation (1.4).
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace Runcorn

/-- Degree and basis index for one spherical harmonic. -/
abbrev Mode (n : ℕ) := (k : ℕ) × Fin (harmonicDimension n k)

/-- The angular Hilbert space with unnormalized surface area. -/
abbrev AngularL2 (n : ℕ) := Lp ℂ 2 (surfaceMeasure n)

/-- Spherical harmonics on the compact sphere are square-integrable. -/
theorem harmonicMemLp {n k : ℕ} {Z : Sphere n → ℂ} (h : IsSphericalHarmonic k Z) :
    MemLp Z 2 (surfaceMeasure n) := by
  unfold surfaceMeasure
  exact h.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The equivalence class of a chosen orthogonal basis function. -/
def angularVector {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (a : Mode n) : AngularL2 n :=
  (harmonicMemLp ((hY a.1).1 a.2)).toLp (Y a.1 a.2)

/-- Passing to L² preserves the basis function almost everywhere. -/
theorem angularVector_coe_ae {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (a : Mode n) : (angularVector Y hY a : Sphere n → ℂ) =ᵐ[surfaceMeasure n] Y a.1 a.2 :=
  MemLp.coeFn_toLp _

/-- Angular pairings use the paper's conjugation convention. -/
theorem angularVector_inner {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (a : Mode n) (F : AngularL2 n) :
    inner ℂ (angularVector Y hY a) F =
      ∫ σ, F σ * conj (Y a.1 a.2 σ) ∂surfaceMeasure n := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [angularVector_coe_ae Y hY a] with σ hσ
  rw [RCLike.inner_apply, hσ]

/-- The angular Gram matrix specializes to the surface integral on basis vectors. -/
theorem angularVector_inner_basis {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (a b : Mode n) :
    inner ℂ (angularVector Y hY a) (angularVector Y hY b) =
      ∫ σ, Y b.1 b.2 σ * conj (Y a.1 a.2 σ) ∂surfaceMeasure n := by
  rw [angularVector_inner]
  apply integral_congr_ae
  filter_upwards [angularVector_coe_ae Y hY b] with σ hσ
  rw [hσ]

/-- Every angular basis vector is nonzero in the actual L² space. -/
theorem angularVector_ne_zero {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (a : Mode n) : angularVector Y hY a ≠ 0 := by
  intro hz
  apply angularMass_ne_zero Y hY a.1 a.2
  rw [← angularVector_inner_basis Y hY a a, hz, inner_zero_left]

/-- Coefficient of an arbitrary L² function along a possibly unnormalized basis vector. -/
def angularCoefficient {n : ℕ} (Y : AngularFamily n) (F : AngularL2 n) (a : Mode n) : ℂ :=
  (∫ σ, F σ * conj (Y a.1 a.2 σ) ∂surfaceMeasure n) /
    (∫ σ, Y a.1 a.2 σ * conj (Y a.1 a.2 σ) ∂surfaceMeasure n)

/-- Orthogonal series for a complete, possibly unnormalized family in a complex Hilbert space. -/
theorem hasSum_orthogonal_coefficients {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (w : ι → H) (hne : ∀ i, w i ≠ 0)
    (hortho : Pairwise (fun i j ↦ inner ℂ (w i) (w j) = 0))
    (hdense : (Submodule.span ℂ (Set.range w)).topologicalClosure = ⊤) (x : H) :
    HasSum (fun i ↦ (inner ℂ (w i) x / inner ℂ (w i) (w i)) • w i) x := by
  let v : ι → H := fun i ↦ ((‖w i‖ : ℂ)⁻¹) • w i
  have hvnorm (i : ι) : ‖v i‖ = 1 := by
    simp [v, norm_smul, hne i]
  have hv : Orthonormal ℂ v := by
    refine ⟨hvnorm, ?_⟩
    intro i j hij
    simp [v, inner_smul_left, inner_smul_right, hortho hij]
  have hsub : Submodule.span ℂ (Set.range w) ≤ Submodule.span ℂ (Set.range v) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi := (Submodule.span ℂ (Set.range v)).smul_mem (‖w i‖ : ℂ)
      (Submodule.subset_span (Set.mem_range_self i))
    simpa [v, smul_smul, hne i] using hi
  have hspan : ⊤ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure :=
    hdense ▸ Submodule.topologicalClosure_mono hsub
  let b := HilbertBasis.mk hv hspan
  have hb (i : ι) : b i = v i := congrFun (HilbertBasis.coe_mk hv hspan) i
  have hsum := b.hasSum_repr x
  convert hsum using 1
  funext i
  rw [b.repr_apply_apply, hb, inner_self_eq_norm_sq_to_K, inner_smul_left, smul_smul]
  congr 1
  simp [div_eq_mul_inv, sq]
  ring

/-- The spherical harmonic series converges in angular L² by degree. The analytic
inputs remaining here are orthogonality for differing degrees and density of their span. -/
theorem angular_degree_sums_tendsto {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (hcross : ∀ a b : Mode n, a.1 ≠ b.1 →
      (∫ σ, Y b.1 b.2 σ * conj (Y a.1 a.2 σ) ∂surfaceMeasure n) = 0)
    (hdense : (Submodule.span ℂ (Set.range (angularVector Y hY))).topologicalClosure = ⊤)
    (F : AngularL2 n) :
    Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range N, ∑ j : Fin (harmonicDimension n k),
      angularCoefficient Y F ⟨k,j⟩ • angularVector Y hY ⟨k,j⟩) atTop (𝓝 F) := by
  have hortho : Pairwise (fun a b : Mode n ↦
      inner ℂ (angularVector Y hY a) (angularVector Y hY b) = 0) := by
    rintro ⟨k,i⟩ ⟨l,j⟩ hne
    rw [angularVector_inner_basis]
    by_cases hkl : k = l
    · subst l
      exact (hY k).2.2.2 j i (fun hji ↦ hne (by cases hji; rfl))
    · exact hcross ⟨k,i⟩ ⟨l,j⟩ hkl
  have hs := hasSum_orthogonal_coefficients (angularVector Y hY) (angularVector_ne_zero Y hY)
    hortho hdense F
  simp_rw [angularVector_inner_basis, angularVector_inner] at hs
  change HasSum (fun a : Mode n ↦ angularCoefficient Y F a • angularVector Y hY a) F at hs
  exact (hs.sigma (fun _ ↦ hasSum_fintype _)).tendsto_sum_nat

end Runcorn
