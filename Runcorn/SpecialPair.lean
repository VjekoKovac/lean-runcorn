module

public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The null-vector tests of Kovač and Smolić, Lemma 4

Real Fréchet derivatives act on Euclidean coordinate directions. All scalar
products between complex vectors in this calculation are bilinear.
-/
@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Runcorn.SpecialPair

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

/-- The complex-valued real-linear form with coefficients ζ. -/
def form (ζ : Fin n → ℂ) : E →L[ℝ] ℂ :=
  ∑ i, ζ i • Complex.ofRealCLM.comp (EuclideanSpace.proj i)

theorem form_apply (ζ : Fin n → ℂ) (x : E) :
    form ζ x = ∑ i, ζ i * (x i : ℂ) := by
  simp [form, EuclideanSpace.proj, PiLp.proj_apply]

@[simp] theorem form_single (ζ : Fin n → ℂ) (i : Fin n) :
    form ζ (e i) = ζ i := by
  simp [form_apply, EuclideanSpace.single, PiLp.single_apply, apply_ite]

/-- Real directional derivative of the complexified integer power of radius. -/
theorem radial_derivative (s : ℤ) {x : E} (hx : x ≠ 0) (i : Fin n) :
    fderiv ℝ (fun y : E => ((‖y‖ ^ s : ℝ) : ℂ)) x (e i) =
      (s : ℂ) * (‖x‖ ^ (s-2) : ℝ) * (x i : ℂ) := by
  have h0 := norm_ne_zero_iff.mpr hx
  have hnorm : HasFDerivAt (fun y : E => ‖y‖)
      ((1 / (2 * ‖x‖)) • (2 • innerSL ℝ x)) x := by
    simpa using (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 h0)
  have hh := Complex.ofRealCLM.hasFDerivAt.comp x
    ((hasDerivAt_zpow s ‖x‖ (Or.inl h0)).comp_hasFDerivAt x hnorm)
  change (fderiv ℝ (Complex.ofRealCLM ∘ (fun r : ℝ => r ^ s) ∘ (fun y : E => ‖y‖)) x) (e i) = _
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul,
    innerSL_apply_apply, EuclideanSpace.inner_single_right, RCLike.conj_to_real,
    one_mul, Complex.ofRealCLM_apply]
  norm_cast
  rw [show s-1 = (s-2)+1 by omega, zpow_add_one₀ h0]
  field_simp
  ring

theorem radial_differentiable (s : ℤ) {x : E} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : E => ((‖y‖ ^ s : ℝ) : ℂ)) x := by
  have h := (hasDerivAt_zpow s ‖x‖ (Or.inl (norm_ne_zero_iff.mpr hx))).differentiableAt
  exact Complex.ofRealCLM.differentiableAt.comp x
    (h.comp x (differentiableAt_id.norm ℝ hx))

theorem power_derivative (ζ : Fin n → ℂ) (p : ℕ) (x : E) (i : Fin n) :
    fderiv ℝ (fun y => form ζ y ^ p) x (e i) =
      p * form ζ x ^ (p - 1) * ζ i := by
  rw [((form ζ).hasFDerivAt.pow p).fderiv]
  simp [nsmul_eq_mul]

/-- Coordinate formula for the exterior test, with arbitrary integer radial exponent. -/
theorem radialPower_derivative (ζ : Fin n → ℂ) (s : ℤ) (q : ℕ)
    {x : E} (hx : x ≠ 0) (i : Fin n) :
    fderiv ℝ (fun y : E => ((‖y‖ ^ s : ℝ) : ℂ) * form ζ y ^ q) x (e i) =
      (‖x‖ ^ s : ℝ) * (q * form ζ x ^ (q-1) * ζ i) +
      form ζ x ^ q * ((s : ℂ) * (‖x‖ ^ (s-2) : ℝ) * (x i : ℂ)) := by
  have hq : DifferentiableAt ℝ (fun y => form ζ y ^ q) x :=
    ((form ζ).hasFDerivAt.pow q).differentiableAt
  rw [fderiv_fun_mul (radial_differentiable s hx) hq]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [radial_derivative s hx i, power_derivative]

/-- The pointwise identity (2.5), generalized to any integer radial exponent.
The null condition eliminates the derivative of the second polynomial factor. -/
theorem gradient_product (ζ : Fin n → ℂ) (hζ : ∑ i, ζ i ^ 2 = 0)
    (p q : ℕ) (hp : 1 ≤ p) (s : ℤ) {x : E} (hx : x ≠ 0) :
    (∑ i, fderiv ℝ (fun y => form ζ y ^ p) x (e i) *
      fderiv ℝ (fun y : E => ((‖y‖ ^ s : ℝ) : ℂ) * form ζ y ^ q) x (e i)) =
      p * (s : ℂ) * (‖x‖ ^ (s-2) : ℝ) * form ζ x ^ (p+q) := by
  let A : ℂ := p * form ζ x ^ (p-1)
  let B : ℂ := (‖x‖ ^ s : ℝ) * q * form ζ x ^ (q-1)
  let D : ℂ := form ζ x ^ q * s * (‖x‖ ^ (s-2) : ℝ)
  calc
    _ = ∑ i, (A*B * ζ i ^ 2 + A*D * (ζ i * (x i : ℂ))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [power_derivative, radialPower_derivative ζ s q hx i]
      dsimp [A,B,D]
      ring
    _ = A * D * form ζ x := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hζ, ← form_apply]
      ring
    _ = _ := by
      have he : p+q = (p-1)+q+1 := by omega
      rw [he, pow_add, pow_add, pow_one]
      dsimp [A,D]
      ring

end Runcorn.SpecialPair
