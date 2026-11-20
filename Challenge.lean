module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Independent Comparator reference for arXiv:2607.18379v1, Theorems 1 and 2

Functions are represented on the ambient space. Only the specified open sets,
closed annulus, or restricted measures enter the conditions below.
This Mathlib-only reference elaborates in isolation from the implementation.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators ComplexConjugate

namespace Runcorn

/-- The ambient real Euclidean space with its standard norm and Lebesgue measure. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
/-- The unit sphere in the ambient Euclidean space. -/
abbrev Sphere (n : ℕ) := Metric.sphere (0 : Space n) 1

/-- Euclidean surface area on the unit sphere from the polar decomposition of Lebesgue measure. -/
def surfaceMeasure (n : ℕ) : Measure (Sphere n) :=
  (volume : Measure (Space n)).toSphere

/-- The closed annulus with inner radius a and outer radius b, equation (1.1c). -/
def annulus {n : ℕ} (a b : ℝ) : Set (Space n) :=
  {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}

/-- The intersection of the open ball of radius hi and the exterior of the closed ball of radius lo. -/
def shell {n : ℕ} (lo hi : ℝ) : Set (Space n) :=
  {x | lo < ‖x‖ ∧ ‖x‖ < hi}

/-- Real coordinate derivatives, with the complex bilinear dot product of (1.2). -/
def gradDot {n : ℕ} (u v : Space n → ℂ) (x : Space n) : ℂ :=
  ∑ i : Fin n, (fderiv ℝ u x (EuclideanSpace.single i 1)) *
    (fderiv ℝ v x (EuclideanSpace.single i 1))

/-- Classical harmonic test functions on their respective open domains. The exterior function tends to zero as its distance from the origin tends to infinity. -/
def Admissible {n : ℕ} (lo hi : ℝ) (u v : Space n → ℂ) : Prop :=
  InnerProductSpace.HarmonicOnNhd u {x | ‖x‖ < hi} ∧
  InnerProductSpace.HarmonicOnNhd v {x | lo < ‖x‖} ∧
  Tendsto v (comap (fun x : Space n ↦ ‖x‖) atTop) (𝓝 0)

/-- Surface integral at positive radius, pulled back to the unit sphere. -/
def surfaceIntegral {n : ℕ} (F : Space n → ℂ) (r : ℝ) : ℂ :=
  (r ^ (n - 1) : ℝ) • ∫ σ : Sphere n, F (r • (σ : Space n)) ∂surfaceMeasure n

/-- Vanishing of the bilinear volume test on one prescribed closed annulus. -/
def FixedTests {n : ℕ} (lo hi a b : ℝ) (f : Space n → ℂ) : Prop :=
  ∀ u v : Space n → ℂ, Admissible lo hi u v →
    (∫ x in annulus a b, f x * gradDot u v x) = 0

/-- Clause (1) of Theorem 1. Every closed subannulus is tested. -/
def AllAnnularTests {n : ℕ} (lo hi : ℝ) (f : Space n → ℂ) : Prop :=
  ∀ a b : ℝ, lo < a → a < b → b < hi → FixedTests lo hi a b f

/-- Clause (2) of Theorem 1. Every sphere of intermediate radius is tested. -/
def AllSurfaceTests {n : ℕ} (lo hi : ℝ) (f : Space n → ℂ) : Prop :=
  ∀ r ∈ Ioo lo hi, ∀ u v : Space n → ℂ, Admissible lo hi u v →
    surfaceIntegral (fun x ↦ f x * gradDot u v x) r = 0

/-- Pointwise radiality on the open shell. -/
def RadialOn {n : ℕ} (lo hi : ℝ) (f : Space n → ℂ) : Prop :=
  ∃ g : ℝ → ℂ, ∀ x ∈ shell lo hi, f x = g ‖x‖

/-- Used at n = 2, its two coordinates are r cos φ and r sin φ. -/
def polarPoint (n : ℕ) (r φ : ℝ) : Space n :=
  WithLp.toLp 2 (fun i : Fin n ↦ if i.val = 0 then r * Real.cos φ else r * Real.sin φ)

/-- The three Fourier modes of the planar conclusion, with continuous radial profiles. -/
def ThreeModes {n : ℕ} (lo hi : ℝ) (f : Space n → ℂ) : Prop :=
  ∃ gMinus gZero gPlus : ℝ → ℂ,
    ContinuousOn gMinus (Ioo lo hi) ∧ ContinuousOn gZero (Ioo lo hi) ∧
    ContinuousOn gPlus (Ioo lo hi) ∧
    ∀ r ∈ Ioo lo hi, ∀ φ : ℝ, f (polarPoint n r φ) =
      gMinus r * Complex.exp (-Complex.I * (φ : ℂ)) + gZero r +
      gPlus r * Complex.exp (Complex.I * (φ : ℂ))

/-- The dimension-dependent angular classification in clause (3) of Theorem 1. -/
def AngularForm {n : ℕ} (lo hi : ℝ) (f : Space n → ℂ) : Prop :=
  (3 ≤ n → RadialOn lo hi f) ∧ (n = 2 → ThreeModes lo hi f)

/-- Theorem 1, including the entire three-way equivalence. -/
def VaryingStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ lo hi : ℝ, 0 < lo → lo < hi →
  ∀ f : Space n → ℂ, ContinuousOn f (shell lo hi) →
    (AllAnnularTests lo hi f ↔ AllSurfaceTests lo hi f) ∧
    (AllAnnularTests lo hi f ↔ AngularForm lo hi f)

/-- Dimension formula preceding Theorem 2. The index j : Fin (harmonicDimension n k)
corresponds to index j+1 in the paper. -/
def harmonicDimension (n k : ℕ) : ℕ :=
  if k = 0 then 1 else if k = 1 then n else
    Nat.choose (n + k - 1) (n - 1) - Nat.choose (n + k - 3) (n - 1)

/-- Evaluation of a complex polynomial in n variables at the real coordinates of x. -/
def polynomialValue {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (x : Space n) : ℂ :=
  MvPolynomial.eval (fun i ↦ (x i : ℂ)) P

/-- Restriction to the unit sphere of a homogeneous degree-k polynomial harmonic on all of the ambient space. -/
def IsSphericalHarmonic {n : ℕ} (k : ℕ) (Y : Sphere n → ℂ) : Prop :=
  ∃ P : MvPolynomial (Fin n) ℂ, P.IsHomogeneous k ∧
    InnerProductSpace.HarmonicOnNhd (polynomialValue P) univ ∧
    ∀ σ : Sphere n, Y σ = polynomialValue P σ.val

/-- A finite family of spherical functions in each degree with indices shifted to start at zero. -/
abbrev AngularFamily (n : ℕ) := (k : ℕ) → Fin (harmonicDimension n k) → Sphere n → ℂ

/-- Membership, linear independence, spanning and L² orthogonality of each degree's family.
Normalizing its elements to unit norm is unnecessary. -/
def IsAngularBasis {n : ℕ} (Y : AngularFamily n) : Prop :=
  ∀ k : ℕ, (∀ j, IsSphericalHarmonic k (Y k j)) ∧
    LinearIndependent ℂ (Y k) ∧
    (∀ Z : Sphere n → ℂ, IsSphericalHarmonic k Z →
      ∃ c : Fin (harmonicDimension n k) → ℂ, ∀ σ : Sphere n, Z σ = ∑ j, c j * Y k j σ) ∧
    ∀ i j, i ≠ j → (∫ σ : Sphere n, Y k i σ * conj (Y k j σ) ∂surfaceMeasure n) = 0

/-- Precisely the integer exponents of the finite Laurent monomial set ℜ_k.
The planar range is written l+2 ≤ k to handle k=0,1 without truncated subtraction. -/
def momentExponent (n k : ℕ) (m : ℤ) : Prop :=
  if n = 2 then
    ∃ l : ℕ, l + 2 ≤ k ∧ m = 2 * (l : ℤ) - (k : ℤ)
  else
    ∃ l : ℕ, l < k ∧ m = 2 * (l : ℤ) - (k : ℤ) - (n : ℤ) + 2

/-- The radial volume measure on the closed real interval, with density r^(n−1). -/
def radialMeasure (n : ℕ) (a b : ℝ) : Measure ℝ :=
  (volume.restrict (Icc a b)).withDensity (fun r ↦ ENNReal.ofReal (r ^ (n - 1)))

/-- Membership of a representative in 𝔊_k. The Laurent monomials are real. -/
def InMomentSpace (n k : ℕ) (a b : ℝ) (g : ℝ → ℂ) : Prop :=
  MemLp g 2 (radialMeasure n a b) ∧
  ∀ m : ℤ, momentExponent n k m →
    (∫ r, g r * ((r ^ m : ℝ) : ℂ) ∂radialMeasure n a b) = 0

/-- Radial coefficient functions for each basis index and each spherical harmonic degree. -/
abbrev Coefficients (n : ℕ) := (k : ℕ) → Fin (harmonicDimension n k) → ℝ → ℂ

/-- Evaluate a spherical function at the direction of x. The value at x=0 is immaterial
on the annuli of the theorem. -/
def atDirection {n : ℕ} (Y : Sphere n → ℂ) (x : Space n) : ℂ := by
  classical
  let σ := ‖x‖⁻¹ • x
  exact if h : σ ∈ Metric.sphere (0 : Space n) 1 then Y ⟨σ, h⟩ else 0

/-- Sum of all spherical harmonic terms of degree strictly less than N. -/
def partialExpansion {n : ℕ} (Y : AngularFamily n) (g : Coefficients n)
    (N : ℕ) (x : Space n) : ℂ :=
  ∑ k ∈ Finset.range N, ∑ j : Fin (harmonicDimension n k), g k j ‖x‖ * atDirection (Y k j) x

/-- Ordered partial sums by spherical degree converge in L² of the closed annulus.
This uses the extended L² seminorm on representatives of equivalence classes. -/
def HasMomentExpansion {n : ℕ} (a b : ℝ) (Y : AngularFamily n) (f : Space n → ℂ) : Prop :=
  ∃ g : Coefficients n,
    (∀ k j, InMomentSpace n k a b (g k j)) ∧
    (∀ N, MemLp (partialExpansion Y g N) 2 (volume.restrict (annulus a b))) ∧
    Tendsto (fun N : ℕ ↦ eLpNorm (fun x ↦ partialExpansion Y g N x - f x)
      2 (volume.restrict (annulus a b))) atTop (𝓝 0)

/-- Theorem 2 for any orthogonal basis chosen in each degree. -/
def FixedStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ lo hi a b : ℝ, 0 < lo → lo < a → a < b → b < hi →
  ∀ Y : AngularFamily n, IsAngularBasis Y →
  ∀ f : Space n → ℂ, MemLp f 2 (volume.restrict (annulus a b)) →
    (FixedTests lo hi a b f ↔ HasMomentExpansion a b Y f)

/-- arXiv:2607.18379v1, Theorem 1. -/
theorem varyingAnnuli (n : ℕ) (hn : 2 ≤ n) (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo < hi)
    (f : Space n → ℂ) (hf : ContinuousOn f (shell lo hi)) :
    (AllAnnularTests lo hi f ↔ AllSurfaceTests lo hi f) ∧
    (AllAnnularTests lo hi f ↔ AngularForm lo hi f) := by sorry

/-- arXiv:2607.18379v1, Theorem 2. -/
theorem fixedAnnulus (n : ℕ) (hn : 2 ≤ n) (lo hi a b : ℝ) (hlo : 0 < lo) (ha : lo < a)
    (hab : a < b) (hb : b < hi) (Y : AngularFamily n) (hY : IsAngularBasis Y)
    (f : Space n → ℂ) (hf : MemLp f 2 (volume.restrict (annulus a b))) :
    FixedTests lo hi a b f ↔ HasMomentExpansion a b Y f := by sorry

end Runcorn
