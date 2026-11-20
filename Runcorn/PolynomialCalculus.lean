module

public import Runcorn.Definitions
public import Runcorn.Algebra
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Polynomial and Euclidean Laplacians

Coordinate evaluation intertwines the formal partial derivatives and the real
Fréchet derivatives of a complex polynomial on Euclidean space. This is the
link between the Fischer calculation in Section 2 and the harmonicity
predicate in the two main statements.
-/

@[expose] public section
noncomputable section
open Filter MvPolynomial InnerProductSpace Laplacian
open scoped Topology
namespace Runcorn
variable {n : ℕ}
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

theorem polynomialValue_C (c : ℂ) :
    polynomialValue (n := n) (C c) = fun _ => c := by
  funext x; simp [polynomialValue]

theorem polynomialValue_X (j : Fin n) :
    polynomialValue (X j) = Complex.ofRealCLM.comp (EuclideanSpace.proj j) := by
  funext x; simp [polynomialValue, EuclideanSpace.proj]

theorem polynomialValue_add (P Q : Polynomial.Poly n) :
    polynomialValue (P + Q) = fun x => polynomialValue P x + polynomialValue Q x := by
  funext x; simp [polynomialValue]

theorem polynomialValue_mul (P Q : Polynomial.Poly n) :
    polynomialValue (P * Q) = fun x => polynomialValue P x * polynomialValue Q x := by
  funext x; simp [polynomialValue]

theorem contDiff_polynomialValue (P : Polynomial.Poly n) (d : WithTop ℕ∞) :
    ContDiff ℝ d (polynomialValue P) := by
  induction P using MvPolynomial.induction_on with
  | C => rw [polynomialValue_C]; exact contDiff_const
  | add P Q hP hQ => rw [polynomialValue_add]; exact hP.add hQ
  | mul_X P j hP =>
    rw [polynomialValue_mul, polynomialValue_X]
    exact hP.mul (ContinuousLinearMap.contDiff _)

theorem polynomialValue_partial (P : Polynomial.Poly n) (i : Fin n) (x : Space n) :
    fderiv ℝ (polynomialValue P) x (e i) = polynomialValue (pderiv i P) x := by
  have diff (Q : Polynomial.Poly n) := (contDiff_polynomialValue Q 1).differentiable (by decide) x
  have xder (j : Fin n) :
      fderiv ℝ (polynomialValue (X j)) x (e i) = polynomialValue (pderiv i (X j)) x := by
    rw [polynomialValue_X, ContinuousLinearMap.fderiv]
    by_cases h : i = j
    · subst j
      simp [polynomialValue, EuclideanSpace.proj, PiLp.proj_apply]
    · simp [polynomialValue, pderiv_X_of_ne (Ne.symm h), EuclideanSpace.proj, Ne.symm h]
  induction P using MvPolynomial.induction_on with
  | C => simp [polynomialValue_C, polynomialValue]
  | add P Q hP hQ =>
    rw [polynomialValue_add, fderiv_fun_add (diff P) (diff Q), map_add, polynomialValue_add]
    simp [hP,hQ]
  | mul_X P j hP =>
    rw [polynomialValue_mul, fderiv_fun_mul (diff P) (diff (X j)), pderiv_mul,
      polynomialValue_add, polynomialValue_mul, polynomialValue_mul]
    simp only [add_apply, smul_apply, smul_eq_mul, hP, xder]
    ring

/-- For a C² function the Euclidean Laplacian is the sum of the iterated
directional derivatives along the coordinate unit vectors. -/
theorem laplacian_eq_sum_partials {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : Space n → G} {x : Space n} (h : ContDiffAt ℝ 2 F x) :
    Δ F x = ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ F y (e i)) x (e i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis F (EuclideanSpace.basisFun (Fin n) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by decide)
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const (e i))]
  simp [EuclideanSpace.basisFun_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem laplacian_polynomialValue (P : Polynomial.Poly n) :
    Δ (polynomialValue P) = polynomialValue (Polynomial.lap P) := by
  funext x
  rw [laplacian_eq_sum_partials (contDiff_polynomialValue P 2).contDiffAt]
  have each (i : Fin n) : (fun y => fderiv ℝ (polynomialValue P) y (e i)) =
      polynomialValue (pderiv i P) := funext (polynomialValue_partial P i)
  simp_rw [each, polynomialValue_partial]
  simp [Polynomial.lap, polynomialValue]

theorem harmonic_polynomialValue (P : Polynomial.Poly n) (h : Polynomial.lap P = 0) :
    HarmonicOnNhd (polynomialValue P) Set.univ := by
  intro x _
  refine ⟨(contDiff_polynomialValue P 2).contDiffAt, ?_⟩
  exact Filter.Eventually.of_forall fun y => by
    rw [laplacian_polynomialValue, h]; simp [polynomialValue]

end Runcorn
