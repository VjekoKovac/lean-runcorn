module

public import Runcorn.RadialSeries
public import Runcorn.SphericalCompleteness
public import Runcorn.Orthogonality
public import Runcorn.AngularSpan
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Spherical series for scalar L² on a radial product space

Fubini gives square-integrable angular slices almost everywhere. Finite expansions
give a measurable sequence converging to their L² classes, which proves strong
measurability of the slice field. This permits the radial dominated-convergence
argument without any regularity assumption on the original scalar function.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace Runcorn

/-- The scalar coefficient in equation (1.4) at a radius r. -/
def productCoefficient {n : ℕ} (Y : AngularFamily n) (f : ℝ × Sphere n → ℂ)
    (a : Mode n) (r : ℝ) : ℂ :=
  (∫ σ, f (r, σ) * conj (Y a.1 a.2 σ) ∂surfaceMeasure n) /
    (∫ σ, Y a.1 a.2 σ * conj (Y a.1 a.2 σ) ∂surfaceMeasure n)

/-- The degree-ordered partial sum in product coordinates. -/
def productPartial {n : ℕ} (Y : AngularFamily n) (f : ℝ × Sphere n → ℂ)
    (N : ℕ) (p : ℝ × Sphere n) : ℂ :=
  ∑ k ∈ Finset.range N, ∑ j : Fin (harmonicDimension n k),
    productCoefficient Y f ⟨k,j⟩ p.1 * Y k j p.2

/-- The squared complex L² norm is the integral of the squared pointwise norm. -/
theorem complexL2_norm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X} (G : Lp ℂ 2 μ) :
    ‖G‖ ^ 2 = ∫ x, ‖G x‖ ^ 2 ∂μ := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) G
  rw [L2.inner_def] at h
  simp_rw [RCLike.inner_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  rw [integral_complex_ofReal] at h
  change ((∫ x, ‖G x‖ ^ 2 ∂μ : ℝ) : ℂ) = (‖G‖ : ℂ)^2 at h
  exact_mod_cast h.symm

private theorem field_congr_coefficient {n : ℕ} (Y : AngularFamily n)
    (f : ℝ × Sphere n → ℂ) (F : AngularL2 n) (r : ℝ)
    (h : (F : Sphere n → ℂ) =ᵐ[surfaceMeasure n] fun σ ↦ f (r, σ)) (a : Mode n) :
    angularCoefficient Y F a = productCoefficient Y f a r := by
  unfold angularCoefficient productCoefficient
  congr 1
  apply integral_congr_ae
  filter_upwards [h] with σ hσ
  rw [hσ]

/-- L² on a product yields a strongly measurable, square-integrable field of angular
L² slices. The almost-everywhere equality uses the two measures in their proper order. -/
theorem exists_angular_slice_field {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (hcross : ∀ a b : Mode n, a.1 ≠ b.1 →
      (∫ σ, Y b.1 b.2 σ * conj (Y a.1 a.2 σ) ∂surfaceMeasure n) = 0)
    (hdense : (Submodule.span ℂ (Set.range (angularVector Y hY))).topologicalClosure = ⊤)
    {μ : Measure ℝ} [SFinite μ] (f : ℝ × Sphere n → ℂ) (hf : MemLp f 2 (μ.prod (surfaceMeasure n))) :
    ∃ F : ℝ → AngularL2 n, MemLp F 2 μ ∧
      ∀ᵐ r ∂μ, (F r : Sphere n → ℂ) =ᵐ[surfaceMeasure n] fun σ ↦ f (r,σ) := by
  classical
  let : IsFiniteMeasure (surfaceMeasure n) := by unfold surfaceMeasure; infer_instance
  have hsq := hf.integrable_norm_pow (by decide : 2 ≠ 0)
  have hs : ∀ᵐ r ∂μ, MemLp (fun σ ↦ f (r,σ)) 2 (surfaceMeasure n) := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left, hsq.prod_right_ae] with r hmeas hi
    exact (memLp_two_iff_integrable_sq_norm hmeas).mpr hi
  let F : ℝ → AngularL2 n := fun r ↦
    if h : MemLp (fun σ ↦ f (r,σ)) 2 (surfaceMeasure n) then h.toLp _ else 0
  have hag : ∀ᵐ r ∂μ, (F r : Sphere n → ℂ) =ᵐ[surfaceMeasure n] fun σ ↦ f (r,σ) := by
    filter_upwards [hs] with r hr
    simpa [F, hr] using hr.coeFn_toLp
  have hmcoef (a : Mode n) : AEStronglyMeasurable (productCoefficient Y f a) μ := by
    have hy := (Complex.continuous_conj.comp ((hY a.1).1 a.2).continuous).aestronglyMeasurable
      (μ := surfaceMeasure n)
    have hm := (hf.aestronglyMeasurable.mul hy.comp_snd).integral_prod_right'
    have hm' : AEStronglyMeasurable
        (fun r ↦ ∫ σ, f (r,σ) * conj (Y a.1 a.2 σ) ∂surfaceMeasure n) μ := hm
    unfold productCoefficient
    simp only [div_eq_mul_inv]
    exact hm'.mul aestronglyMeasurable_const
  let T : ℕ → ℝ → AngularL2 n := fun N r ↦ ∑ k ∈ Finset.range N,
    ∑ j : Fin (harmonicDimension n k), productCoefficient Y f ⟨k,j⟩ r • angularVector Y hY ⟨k,j⟩
  have hmT (N : ℕ) : AEStronglyMeasurable (T N) μ := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro k _
    apply Finset.aestronglyMeasurable_fun_sum
    intro j _
    exact (hmcoef ⟨k,j⟩).smul aestronglyMeasurable_const
  have hconv : ∀ᵐ r ∂μ, Tendsto (fun N ↦ T N r) atTop (𝓝 (F r)) := by
    filter_upwards [hag] with r hr
    simpa only [T, ← field_congr_coefficient Y f (F r) r hr] using
      angular_degree_sums_tendsto Y hY hcross hdense (F r)
  have hmF := aestronglyMeasurable_of_tendsto_ae atTop hmT hconv
  refine ⟨F, (memLp_two_iff_integrable_sq_norm hmF).mpr ?_, hag⟩
  apply hsq.integral_prod_left.congr
  filter_upwards [hag] with r hr
  rw [complexL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hr] with σ hσ
  rw [hσ]

private theorem product_tensor_memLp {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    {μ : Measure X} {ν : Measure T} {f : X → ℂ} {g : T → ℂ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 ν) : MemLp (fun z : X × T ↦ f z.1 * g z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm (hf.aestronglyMeasurable.comp_fst.mul hg.aestronglyMeasurable.comp_snd)).mpr
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using
    (hf.integrable_norm_pow (by decide : 2 ≠ 0)).mul_prod (hg.integrable_norm_pow (by decide : 2 ≠ 0))

private theorem ae_sum_functions {X A ι : Type*} [MeasurableSpace X] [AddCommMonoid A]
    {μ : Measure X} {s : Finset ι} {f g : ι → X → A} (h : ∀ i ∈ s, f i =ᵐ[μ] g i) :
    (fun x ↦ ∑ i ∈ s, f i x) =ᵐ[μ] fun x ↦ ∑ i ∈ s, g i x := by
  filter_upwards [eventuallyEq_sum h] with x hx
  simpa only [Finset.sum_apply] using hx

private theorem angularPartial_rep {n : ℕ} (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (f : ℝ × Sphere n → ℂ) (F : AngularL2 n) (r : ℝ)
    (h : (F : Sphere n → ℂ) =ᵐ[surfaceMeasure n] fun σ ↦ f (r,σ)) (N : ℕ) :
    (angularPartial Y hY N F : Sphere n → ℂ) =ᵐ[surfaceMeasure n]
      fun σ ↦ productPartial Y f N (r,σ) := by
  unfold angularPartial productPartial
  grw [Lp.coeFn_fun_finsetSum]
  apply ae_sum_functions
  intro k _
  grw [Lp.coeFn_fun_finsetSum]
  apply ae_sum_functions
  intro j _
  grw [Lp.coeFn_smul, angularVector_coe_ae]
  filter_upwards with σ
  simp [field_congr_coefficient Y f F r h]

/-- All spherical coefficients of a scalar product L² function are radial L² functions.
The degree partial sums converge in the product L² norm, with coefficients from (1.4). -/
theorem product_angular_expansion {n : ℕ} (hn : 2 ≤ n) (Y : AngularFamily n)
    (hY : IsAngularBasis Y) {μ : Measure ℝ} [SFinite μ] (f : ℝ × Sphere n → ℂ)
    (hf : MemLp f 2 (μ.prod (surfaceMeasure n))) :
    (∀ a : Mode n, MemLp (productCoefficient Y f a) 2 μ) ∧
    (∀ N, MemLp (productPartial Y f N) 2 (μ.prod (surfaceMeasure n))) ∧
    Tendsto (fun N ↦ eLpNorm (fun p ↦ productPartial Y f N p - f p) 2
      (μ.prod (surfaceMeasure n))) atTop (𝓝 0) := by
  let : IsFiniteMeasure (surfaceMeasure n) := by unfold surfaceMeasure; infer_instance
  have hcross (a b : Mode n) (hd : a.1 ≠ b.1) :
      (∫ σ, Y b.1 b.2 σ * conj (Y a.1 a.2 σ) ∂surfaceMeasure n) = 0 :=
    integral_mul_eq_zero_of_degree_ne hn hd.symm ((hY b.1).1 b.2) (((hY a.1).1 a.2).conj)
  have hdense := angularBasis_span_dense (by omega : 0 < n) Y hY
  obtain ⟨F,hF,hag⟩ := exists_angular_slice_field Y hY hcross hdense f hf
  have hcoeff (a : Mode n) : MemLp (productCoefficient Y f a) 2 μ := by
    apply (angularCoefficient_memLp Y hY hF a).ae_eq
    filter_upwards [hag] with r hr
    exact field_congr_coefficient Y f (F r) r hr a
  have hpart (N : ℕ) : MemLp (productPartial Y f N) 2 (μ.prod (surfaceMeasure n)) := by
    unfold productPartial
    apply memLp_finsetSum
    intro k _
    apply memLp_finsetSum
    intro j _
    exact product_tensor_memLp (hcoeff ⟨k,j⟩) (harmonicMemLp ((hY k).1 j))
  refine ⟨hcoeff, hpart, ?_⟩
  let err := fun N p ↦ productPartial Y f N p - f p
  have herr (N : ℕ) : MemLp (err N) 2 (μ.prod (surfaceMeasure n)) := (hpart N).sub hf
  have hnorm (N : ℕ) : ‖(herr N).toLp (err N)‖ ^ 2 =
      ∫ r, ‖angularPartial Y hY N (F r) - F r‖ ^ 2 ∂μ := by
    rw [complexL2_norm_sq]
    calc
      _ = ∫ p, ‖err N p‖ ^ 2 ∂μ.prod (surfaceMeasure n) := by
        apply integral_congr_ae
        filter_upwards [(herr N).coeFn_toLp] with p hp
        rw [hp]
      _ = ∫ r, ∫ σ, ‖err N (r,σ)‖ ^ 2 ∂surfaceMeasure n ∂μ :=
        integral_prod _ ((herr N).integrable_norm_pow (by decide : 2 ≠ 0))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hag] with r hr
        rw [complexL2_norm_sq]
        apply integral_congr_ae
        filter_upwards [hr, angularPartial_rep Y hY f (F r) r hr N,
          Lp.coeFn_sub (angularPartial Y hY N (F r)) (F r)] with σ hσ hpart hsub
        rw [hsub]
        change ‖err N (r,σ)‖ ^ 2 = ‖(angularPartial Y hY N (F r)) σ - (F r) σ‖ ^ 2
        rw [hpart, hσ]
  have hlim := radial_integrated_angular_error Y hY hcross hdense F hF
  simp_rw [← hnorm] at hlim
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  have hs : Tendsto (fun N ↦ ‖(herr N).toLp (err N)‖) atTop (𝓝 0) := by
    simpa [Function.comp_def] using hroot
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, ofReal_norm, Lp.enorm_toLp, ENNReal.ofReal_zero] using he

end Runcorn
