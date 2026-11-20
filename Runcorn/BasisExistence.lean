module

public import Runcorn.Dimension
public import Runcorn.SphereDensity
public import Runcorn.Restriction
public import Runcorn.PolynomialHomogeneity
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Existence of the orthogonal basis selected in Theorem 2

The polynomial dimension formula is transported to L² of the actual sphere.
Every polynomial basis vector is represented by its continuous restriction.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped ComplexConjugate InnerProductSpace
namespace Runcorn
namespace Polynomial

private def solidRestriction (n k : ℕ) : solidHarmonics n k →ₗ[ℂ] C(Sphere n,ℂ) where
  toFun P := polynomialOnSphere P.val.val
  map_add' P Q := by ext σ; simp [polynomialOnSphere, polynomialValue]
  map_smul' c P := by ext σ; simp [polynomialOnSphere, polynomialValue,smul_eq_C_mul,smul_eq_mul]

private theorem solidRestriction_injective {n k : ℕ} (hn : 0 < n) :
    Function.Injective (solidRestriction n k) := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  intro P Q h
  apply Subtype.ext
  apply Subtype.ext
  apply polynomialValue_injective
  have heq : EqOn (polynomialValue P.val.val) (polynomialValue Q.val.val) ({(0 : Space n)}ᶜ) := by
    intro x hx
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let σ : Sphere n := ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx0.ne']⟩
    have hrepr : ‖x‖ • σ.val = x := by
      simp [σ, smul_smul, hx0.ne']
    have hp : polynomialValue P.val.val σ.val = polynomialValue Q.val.val σ.val :=
      DFunLike.congr_fun h σ
    rw [← hrepr, polynomialValue_smul_of_homogeneous _ P.val.property,
      polynomialValue_smul_of_homogeneous _ Q.val.property, hp]
  funext x
  exact heq.closure (contDiff_polynomialValue _ 0).continuous
    (contDiff_polynomialValue _ 0).continuous (dense_compl_singleton (0 : Space n) x)

private theorem basis_independent_image {ι E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (b : Module.Basis ι ℂ E) (v : E →ₗ[ℂ] F)
    (hv : Function.Injective v) : LinearIndependent ℂ (fun j ↦ v (b j)) :=
  b.linearIndependent.map' v (LinearMap.ker_eq_bot.mpr hv)

set_option maxHeartbeats 280000 in
private theorem exists_degree_basis {n k : ℕ} (hn : 0 < n) :
    ∃ Y : Fin (harmonicDimension n k) → Sphere n → ℂ,
      (∀ j, IsSphericalHarmonic k (Y j)) ∧ LinearIndependent ℂ Y ∧
      (∀ Z : Sphere n → ℂ, IsSphericalHarmonic k Z →
        ∃ c : Fin (harmonicDimension n k) → ℂ, ∀ σ, Z σ = ∑ j, c j * Y j σ) ∧
      ∀ i j, i ≠ j → (∫ σ : Sphere n, Y i σ * conj (Y j σ) ∂surfaceMeasure n) = 0 := by
  classical
  let μ := surfaceMeasure n
  let : IsFiniteMeasure μ := by dsimp [μ,surfaceMeasure]; infer_instance
  let : μ.IsOpenPosMeasure := by dsimp [μ,surfaceMeasure]; infer_instance
  let T : C(Sphere n,ℂ) →L[ℂ] Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ
  let A := solidRestriction n k
  let L := T.toLinearMap.comp A
  have hA : Function.Injective A := solidRestriction_injective hn
  have hT : Function.Injective T := ContinuousMap.toLp_injective μ
  have hL : Function.Injective L := hT.comp hA
  let E : solidHarmonics n k ≃ₗ[ℂ] L.range := LinearEquiv.ofInjective L hL
  have he : Module.finrank ℂ L.range = harmonicDimension n k :=
    (LinearMap.finrank_range_of_inj hL).trans (finrank_solidHarmonics hn k)
  let b : OrthonormalBasis (Fin (harmonicDimension n k)) ℂ L.range := (stdOrthonormalBasis ℂ L.range).reindex (finCongr he)
  let bP : Module.Basis (Fin (harmonicDimension n k)) ℂ (solidHarmonics n k) := b.toBasis.map E.symm
  let V : solidHarmonics n k →ₗ[ℂ] (Sphere n → ℂ) :=
    (ContinuousMap.coeFnLinearMap ℂ).comp A
  have hV : Function.Injective V := DFunLike.coe_injective.comp hA
  refine ⟨fun j ↦ V (bP j), fun j ↦ ?_, ?_, ?_, ?_⟩
  · clear_value bP
    let P := bP j
    refine ⟨P.val.val, P.val.property, harmonic_polynomialValue _ ?_, fun _ ↦ rfl⟩
    have hP : lapLinear n k P.val = 0 := P.property
    exact congrArg Subtype.val hP
  · clear_value bP V
    exact @basis_independent_image (Fin (harmonicDimension n k)) (solidHarmonics n k)
      (Sphere n → ℂ) _ _ _ _ bP V hV
  · clear_value bP
    rintro Z ⟨P,hdeg,hh,hZ⟩
    let p : solidHarmonics n k := ⟨⟨P,hdeg⟩, Subtype.ext (polynomial_lap_eq_zero_of_harmonic P hh)⟩
    refine ⟨fun j ↦ bP.repr p j, fun σ ↦ ?_⟩
    rw [hZ σ]
    change V p σ = _
    calc
      V p σ = V (∑ j, bP.repr p j • bP j) σ := congrArg (fun a ↦ V a σ) (bP.sum_repr p).symm
      _ = _ := by simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  · clear_value b
    intro i j hij
    have hb (a : Fin (harmonicDimension n k)) : T (A (bP a)) = (b a).val := by
      change (E (E.symm (b a))).val = (b a).val
      rw [E.apply_symm_apply]
    change (∫ σ, A (bP i) σ * conj (A (bP j) σ) ∂μ) = 0
    rw [← ContinuousMap.inner_toLp μ (A (bP j)) (A (bP i))]
    change inner ℂ (T (A (bP j))) (T (A (bP i))) = 0
    rw [hb,hb]
    exact b.orthonormal.2 hij.symm

end Polynomial

/-- In every dimension covered by the paper, the arbitrary-basis quantifier of
Theorem 2 has an inhabitant, with precisely the dimensions in the statement. -/
theorem exists_angularBasis {n : ℕ} (hn : 0 < n) :
    ∃ Y : AngularFamily n, IsAngularBasis Y := by
  choose Y hY using fun k : ℕ ↦ Polynomial.exists_degree_basis (k := k) hn
  exact ⟨Y,hY⟩

end Runcorn
