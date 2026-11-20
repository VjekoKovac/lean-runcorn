module

public import Runcorn.Algebra
public import Runcorn.Definitions
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The dimension used to index each angular basis

Counting homogeneous monomials gives the ambient dimension. The Laplacian from
degree k+2 onto degree k is surjective: lift each Fischer summand by one power
of the squared radius. Rank-nullity gives the dimension of its kernel.
-/

@[expose] public section
noncomputable section
open MvPolynomial Set
namespace Runcorn.Polynomial

abbrev homogeneousPolys (n k : ℕ) := homogeneousSubmodule (Fin n) ℂ k

instance (n k : ℕ) : FiniteDimensional ℂ (homogeneousPolys n k) :=
  Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)

theorem finrank_homogeneousPolys (n k : ℕ) :
    Module.finrank ℂ (homogeneousPolys n k) = (n+k-1).choose k := by
  classical
  let S := (Finset.univ : Finset (Fin n)).finsuppAntidiag k
  have hs : {d : Fin n →₀ ℕ | d.degree = k} = (S : Set (Fin n →₀ ℕ)) := by
    ext d
    simp [S,Finsupp.degree_eq_sum]
  unfold homogeneousPolys
  rw [homogeneousSubmodule_eq_finsupp_supported, hs]
  rw [(AddMonoidAlgebra.supportedEquivFinsupp (R := ℂ) (S := ℂ) (S : Set (Fin n →₀ ℕ))).finrank_eq,
    Module.finrank_finsupp_self]
  simpa [S] using Finset.card_finsuppAntidiag_nat_eq_choose (s := (Finset.univ : Finset (Fin n))) k

/-- The formal Laplacian on the degree-k homogeneous component. -/
def lapLinear (n k : ℕ) : homogeneousPolys n k →ₗ[ℂ] homogeneousPolys n (k-2) where
  toFun P := ⟨lap P.val, lap_homogeneous P.val P.property⟩
  map_add' P Q := Subtype.ext (lap_add _ _)
  map_smul' c P := by
    apply Subtype.ext
    change lap (c • P.val) = c • lap P.val
    simp [smul_eq_C_mul, lap_const_mul]

/-- Solid harmonic subspace of exact homogeneous degree k. -/
abbrev solidHarmonics (n k : ℕ) := LinearMap.ker (lapLinear n k)

theorem lapLinear_surjective {n : ℕ} (hn : 0 < n) (k : ℕ) :
    Function.Surjective (lapLinear n (k+2)) := by
  intro Q
  let d := (k+2)-2
  obtain ⟨H,hH,he⟩ := exists_fischer hn Q.val Q.property
  let c (l : ℕ) := 2 * ((l:ℂ)+1) * (2 * ((d-2*l : ℕ) : ℂ) + 2*l+n)
  let T (l : ℕ) := C (c l)⁻¹ * (radiusSq n ^ (l+1) * H l)
  have hc (l : ℕ) : c l ≠ 0 := by
    let j := d-2*l
    have hj : 0 < 2 * (l+1) * (2*j+2*l+n) := by exact Nat.mul_pos (by omega) (by omega)
    have hCast : c l = ((2*(l+1)*(2*j+2*l+n) : ℕ) : ℂ) := by
      dsimp [c,j]
      push_cast
      ring
    exact hCast ▸ Nat.cast_ne_zero.mpr hj.ne'
  have hT (l : ℕ) (hl : l ∈ Finset.range (d/2+1)) : (T l).IsHomogeneous (k+2) := by
    have hl' := Finset.mem_range.mp hl
    have h := ((radiusSq_homogeneous.pow (l+1)).mul (hH l (by omega)).1).C_mul (c l)⁻¹
    convert h using 1
    dsimp [d] at *
    omega
  refine ⟨⟨∑ l ∈ Finset.range (d/2+1), T l, IsHomogeneous.sum _ _ _ hT⟩, ?_⟩
  apply Subtype.ext
  change lap (∑ l ∈ Finset.range (d/2+1), T l) = Q.val
  rw [he]
  have hsum {s : Finset ℕ} : lap (∑ l ∈ s, T l) = ∑ l ∈ s, lap (T l) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [lap]
    | insert a s ha ih => simp [ha, lap_add, ih]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro l hl
  have h := hH l (by have := Finset.mem_range.mp hl; omega)
  rw [show T l = C (c l)⁻¹ * _ from rfl, lap_const_mul, lap_radiusSq_pow_succ_mul _ h.1 h.2,
    ← mul_assoc, ← map_mul]
  change C ((c l)⁻¹ * c l) * _ = _
  simp [hc l]

/-- The rank formula from the introduction of the article. -/
theorem finrank_solidHarmonics {n : ℕ} (hn : 0 < n) (k : ℕ) :
    Module.finrank ℂ (solidHarmonics n k) = Runcorn.harmonicDimension n k := by
  rcases k with _ | k
  · have he : lapLinear n 0 = 0 := by
      ext P : 1
      exact Subtype.ext (lap_low_degree _ P.property (by decide))
    unfold solidHarmonics
    rw [LinearMap.ker_eq_top.mpr he, finrank_top, finrank_homogeneousPolys]
    simp [harmonicDimension]
  rcases k with _ | k
  · have he : lapLinear n 1 = 0 := by
      ext P : 1
      exact Subtype.ext (lap_low_degree _ P.property (by decide))
    unfold solidHarmonics
    rw [LinearMap.ker_eq_top.mpr he, finrank_top, finrank_homogeneousPolys]
    simp [harmonicDimension]
  have h := (lapLinear n (k+2)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (lapLinear_surjective hn k), finrank_top, finrank_homogeneousPolys,
    finrank_homogeneousPolys] at h
  change Module.finrank ℂ (LinearMap.ker (lapLinear n (k+2))) = _
  have hs (j : ℕ) : (n+j-1).choose j = (n+j-1).choose (n-1) :=
    Nat.choose_symm_of_eq_add (by omega)
  simp only [harmonicDimension, Nat.add_eq_zero_iff, Nat.reduceEqDiff, and_false, ↓reduceIte,
    Nat.succ_ne_self] 
  have ht : (k+2)-2 = k := by omega
  have hC : (n+(k+2-2)-1).choose (k+2-2) = (n+k-1).choose (n-1) := by rw [ht, hs]
  have hC' := hs (k+2)
  change Module.finrank ℂ (LinearMap.ker (lapLinear n (k+2))) =
    (n+(k+2)-1).choose (n-1) - (n+(k+2)-3).choose (n-1)
  rw [show n+(k+2)-3 = n+k-1 by omega, ← hC, ← hC']
  omega

end Runcorn.Polynomial
