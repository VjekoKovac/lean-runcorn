module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.Ring

/-!
# Polynomial identities for the Runcorn converse

This file follows the polynomial calculations in Section 2 of Kovač and Smolić,
arXiv:2607.18379. Partial derivatives are mathlib's `MvPolynomial.pderiv`.
All products and contractions are complex bilinear.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
open MvPolynomial
namespace Runcorn.Polynomial

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℂ

variable {n : ℕ}

def lap (P : Poly n) : Poly n := ∑ i, pderiv i (pderiv i P)

def linearForm (z : Fin n → ℂ) : Poly n := ∑ i, C (z i) * X i

def radiusSq (n : ℕ) : Poly n := ∑ i : Fin n, X i ^ 2

theorem pderiv_linearForm (z : Fin n → ℂ) (i : Fin n) :
    pderiv i (linearForm z) = C (z i) := by
  classical
  simp [linearForm, map_sum, pderiv_X, Pi.single_apply]

theorem lap_linearForm_pow (z : Fin n → ℂ) (k : ℕ) :
    lap (linearForm z ^ k) =
      (k : Poly n) * ((k - 1 : ℕ) : Poly n) * linearForm z ^ (k - 2) *
        C (∑ i, z i ^ 2) := by
  classical
  unfold lap
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pderiv_pow, pderiv_mul, Derivation.map_natCast, zero_mul, zero_add,
    pderiv_linearForm, pderiv_C, mul_zero, add_zero, map_pow]
  have he : k - 1 - 1 = k - 2 := by omega
  rw [he]
  ring

/-- The inclusion of null powers in the harmonic space in Lemma 3
(the auxiliary lemma labeled `lem:span` in the source). -/
theorem lap_nullForm_pow (z : Fin n → ℂ) (hz : ∑ i, z i ^ 2 = 0) (k : ℕ) :
    lap (linearForm z ^ k) = 0 := by
  rw [lap_linearForm_pow, hz, map_zero, mul_zero]

theorem lap_add (P Q : Poly n) : lap (P + Q) = lap P + lap Q := by
  simp [lap, map_add, Finset.sum_add_distrib]

theorem lap_const_mul (c : ℂ) (P : Poly n) : lap (C c * P) = C c * lap P := by
  simp [lap, Finset.mul_sum]

theorem lap_pderiv (P : Poly n) (j : Fin n) :
    lap (pderiv j P) = pderiv j (lap P) := by
  simp only [lap, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pderiv_comm i j P, pderiv_comm i j (pderiv i P)]

def gradDot (P Q : Poly n) : Poly n := ∑ i, pderiv i P * pderiv i Q

theorem lap_mul (P Q : Poly n) :
    lap (P * Q) = lap P * Q + 2 * gradDot P Q + P * lap Q := by
  simp only [lap, gradDot, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pderiv_mul, map_add]
  ring

/-- The unnormalized contraction of the arrays of partial derivatives of order `s`. -/
def contraction : ℕ → Poly n → Poly n → Poly n
  | 0, P, Q => P * Q
  | s + 1, P, Q => ∑ i, contraction s (pderiv i P) (pderiv i Q)

theorem lap_contraction (s : ℕ) (P Q : Poly n) (hP : lap P = 0) (hQ : lap Q = 0) :
    lap (contraction s P Q) = 2 * contraction (s + 1) P Q := by
  induction s generalizing P Q with
  | zero => simp [contraction, lap_mul, hP, hQ, gradDot]
  | succ s ih =>
    change lap (∑ i, contraction s (pderiv i P) (pderiv i Q)) =
      2 * ∑ i, contraction (s+1) (pderiv i P) (pderiv i Q)
    have hs (f : Fin n → Poly n) : lap (∑ i, f i) = ∑ i, lap (f i) := by
      simp only [lap, map_sum]
      exact Finset.sum_comm
    rw [hs, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      ih _ _ (by simp [lap_pderiv, hP]) (by simp [lap_pderiv, hQ])

theorem iter_lap_mul (s : ℕ) (P Q : Poly n) (hP : lap P = 0) (hQ : lap Q = 0) :
    lap^[s] (P * Q) = 2^s * contraction s P Q := by
  induction s with
  | zero => simp [contraction]
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih]
    have hc : (2 : Poly n)^s = C ((2 : ℂ)^s) := by rw [map_pow, map_ofNat]
    rw [hc, lap_const_mul, lap_contraction s P Q hP hQ, ← hc, pow_succ, mul_assoc]

theorem contraction_zero_left (s : ℕ) (Q : Poly n) : contraction s 0 Q = 0 := by
  induction s generalizing Q with
  | zero => simp [contraction]
  | succ s ih => simp [contraction, ih]

theorem contraction_symm (s : ℕ) (P Q : Poly n) : contraction s P Q = contraction s Q P := by
  induction s generalizing P Q with
  | zero => exact mul_comm _ _
  | succ s ih => exact Finset.sum_congr rfl fun i _ => ih _ _

theorem contraction_eq_zero_of_lt (s p : ℕ) (P Q : Poly n) (hP : P.IsHomogeneous p)
    (hps : p < s) : contraction s P Q = 0 := by
  induction s generalizing p P Q with
  | zero => omega
  | succ s ih =>
    cases p with
    | zero =>
      have hc := (totalDegree_eq_zero_iff_eq_C).mp
        ((totalDegree_zero_iff_isHomogeneous _).mpr hP)
      rw [hc]
      simp [contraction, contraction_zero_left]
    | succ p =>
      apply Finset.sum_eq_zero
      intro i _
      exact ih p _ _ hP.pderiv (by omega)

/-- The vanishing needed to truncate the Fischer decomposition of a product. -/
theorem iter_lap_product_eq_zero (p q : ℕ) (P Q : Poly n) (hp : P.IsHomogeneous p)
    (hq : Q.IsHomogeneous q) (hP : lap P = 0) (hQ : lap Q = 0) :
    lap^[min p q + 1] (P * Q) = 0 := by
  rw [iter_lap_mul _ P Q hP hQ]
  apply mul_eq_zero_of_right
  by_cases h : p ≤ q
  · exact contraction_eq_zero_of_lt _ _ _ _ hp (by omega)
  · rw [contraction_symm]
    exact contraction_eq_zero_of_lt _ _ _ _ hq (by omega)


theorem linearForm_homogeneous (z : Fin n → ℂ) : (linearForm z).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X (z i) i

theorem nullForm_homogeneous (z : Fin n → ℂ) (k : ℕ) :
    (linearForm z ^ k).IsHomogeneous k := by
  simpa only [one_mul] using (linearForm_homogeneous z).pow k

theorem radiusSq_homogeneous : (radiusSq n).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i 2

theorem pderiv_radiusSq (i : Fin n) : pderiv i (radiusSq n) = 2 * X i := by
  classical
  simp [radiusSq, map_sum, pderiv_X, Pi.single_apply]

theorem lap_radiusSq : lap (radiusSq n) = 2 * (n : Poly n) := by
  have htwo (i : Fin n) : pderiv i (2 : Poly n) = 0 := (pderiv i).map_natCast 2
  simp [lap, pderiv_radiusSq, htwo, mul_comm]

theorem lap_radiusSq_mul (P : Poly n) {k : ℕ} (hP : P.IsHomogeneous k) :
    lap (radiusSq n * P) =
      (2 * (n : Poly n) + 4 * (k : Poly n)) * P + radiusSq n * lap P := by
  have he : gradDot (radiusSq n) P = 2 * ((k : Poly n) * P) := by
    simp only [gradDot, pderiv_radiusSq, mul_assoc, ← Finset.mul_sum,
      hP.sum_X_mul_pderiv, nsmul_eq_mul]
  rw [lap_mul, lap_radiusSq, he]
  ring

/-- Polynomial form of the radial Laplacian for even exponents. -/
theorem lap_radiusSq_pow_succ_mul (H : Poly n) {k : ℕ}
    (hh : H.IsHomogeneous k) (hH : lap H = 0) (l : ℕ) :
    lap (radiusSq n ^ (l + 1) * H) =
      C (2 * ((l : ℂ) + 1) * (2 * (k : ℂ) + 2 * (l : ℂ) + n)) *
      (radiusSq n ^ l * H) := by
  induction l with
  | zero =>
    simp only [Nat.cast_zero, zero_add, add_zero, mul_zero, one_mul, pow_zero, pow_one]
    rw [lap_radiusSq_mul H hh, hH]
    simp only [map_mul, map_add, map_natCast, map_ofNat, map_one]
    ring
  | succ l ih =>
    let r := radiusSq n
    have hg : (r ^ (l+1) * H).IsHomogeneous (2 * (l+1) + k) :=
      (radiusSq_homogeneous.pow (l+1)).mul hh
    rw [pow_succ' _ (l+1), mul_assoc, lap_radiusSq_mul _ hg, ih]
    push_cast
    dsimp [r]
    simp only [map_mul, map_add, map_natCast, map_ofNat, map_one]
    ring

theorem lap_homogeneous (P : Poly n) {d : ℕ} (hP : P.IsHomogeneous d) :
    (lap P).IsHomogeneous (d-2) := by
  apply IsHomogeneous.sum
  intro i _
  simpa only [Nat.sub_sub] using (hP.pderiv (i := i)).pderiv (i := i)

theorem iter_lap_homogeneous (P : Poly n) {d : ℕ} (hP : P.IsHomogeneous d) (s : ℕ) :
    (lap^[s] P).IsHomogeneous (d-2*s) := by
  induction s with
  | zero => simpa using hP
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    convert lap_homogeneous _ ih using 1

theorem iter_lap_const_mul (c : ℂ) (P : Poly n) (s : ℕ) :
    lap^[s] (C c * P) = C c * lap^[s] P := by
  induction s with
  | zero => rfl
  | succ s ih => simp only [Function.iterate_succ_apply', ih, lap_const_mul]

theorem iter_lap_sub (P Q : Poly n) (s : ℕ) :
    lap^[s] (P-Q) = lap^[s] P - lap^[s] Q := by
  have hs (A B : Poly n) : lap (A-B) = lap A - lap B := by
    simp only [lap, map_sub, Finset.sum_sub_distrib]
  induction s with
  | zero => rfl
  | succ s ih => simp only [Function.iterate_succ_apply', ih, hs]

/-- Applying precisely `s` Laplacians removes `s` factors of the squared radius
from a harmonic polynomial, up to a nonzero scalar. -/
theorem exists_radial_multiplier (hn : 0 < n) {k : ℕ} (H : Poly n) (hh : H.IsHomogeneous k)
    (hH : lap H = 0) (s : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧ lap^[s] (radiusSq n ^ s * H) = C c * H := by
  induction s with
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | succ s ih =>
    obtain ⟨c, hc, he⟩ := ih
    let t : ℕ := 2 * (s+1) * (2*k+2*s+n)
    have ht : 0 < t := by dsimp [t]; exact Nat.mul_pos (by omega) (by omega)
    refine ⟨(t : ℂ) * c, mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) hc, ?_⟩
    rw [Function.iterate_succ_apply, lap_radiusSq_pow_succ_mul H hh hH s]
    have hcast : (t : ℂ) = 2 * ((s : ℂ)+1) * (2*(k : ℂ)+2*(s : ℂ)+n) := by
      dsimp [t]
      push_cast
      ring
    rw [← hcast, iter_lap_const_mul, he, map_mul, mul_assoc]


/-- Truncated Fischer decomposition. If a homogeneous polynomial of degree `d`
is killed by `s+1` Laplacians, its expansion uses only powers `0,…,s` of
the squared radius. The index restriction avoids negative harmonic degrees. -/
theorem exists_fischer_of_iter_lap_eq_zero (hn : 0 < n) (s d : ℕ)
    (P : Poly n) (hP : P.IsHomogeneous d) (hs : 2*s ≤ d)
    (hvan : lap^[s+1] P = 0) :
    ∃ H : ℕ → Poly n, (∀ l ≤ s, (H l).IsHomogeneous (d-2*l) ∧ lap (H l) = 0) ∧
      P = ∑ l ∈ Finset.range (s+1), radiusSq n ^ l * H l := by
  induction s generalizing P with
  | zero =>
    refine ⟨fun _ => P, ?_, by simp⟩
    intro l hl
    have : l = 0 := by omega
    subst l
    simpa using And.intro hP hvan
  | succ s ih =>
    let t := s+1
    let k := d-2*t
    let D := lap^[t] P
    have hD : D.IsHomogeneous k := iter_lap_homogeneous _ hP t
    have hDz : lap D = 0 := by
      simpa only [D, t, Function.iterate_succ_apply'] using hvan
    obtain ⟨c, hc, hm⟩ := exists_radial_multiplier hn D hD hDz t
    let H := C c⁻¹ * D
    let T := radiusSq n ^ t * H
    have hH : H.IsHomogeneous k := hD.C_mul _
    have hHlap : lap H = 0 := by simp [H, lap_const_mul, hDz]
    have hdeg : 2*t + k = d := by dsimp [k, t] at *; omega
    have hT : T.IsHomogeneous d :=
      hdeg ▸ (radiusSq_homogeneous.pow t).mul hH
    have hTs : lap^[t] T = D := by
      have : T = C c⁻¹ * (radiusSq n ^ t * D) := by dsimp [T, H]; ring
      rw [this, iter_lap_const_mul, hm, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc,
        map_one, one_mul]
    have hrem : lap^[s+1] (P-T) = 0 := by rw [iter_lap_sub, hTs]; exact sub_self _
    obtain ⟨J, hJ, he⟩ := ih (P-T) (hP.sub hT) (by omega) hrem
    refine ⟨Function.update J t H, ?_, ?_⟩
    · intro l hl
      by_cases heq : l = t
      · subst l
        simpa using And.intro hH hHlap
      · simpa [Function.update_of_ne heq] using hJ l (by dsimp [t] at *; omega)
    · rw [Finset.sum_range_succ, show s+1 = t from rfl, Function.update_self]
      have hsum : (∑ l ∈ Finset.range t, radiusSq n ^ l * Function.update J t H l) =
          ∑ l ∈ Finset.range t, radiusSq n ^ l * J l :=
        Finset.sum_congr rfl fun l hl => by
          rw [Function.update_of_ne (Finset.mem_range.mp hl).ne]
      rw [hsum, ← he]
      exact (sub_add_cancel P T).symm

/-- Product decomposition (equation `PQ_truncated`), with its sharp upper index.
This result includes the two-dimensional case. -/
theorem exists_fischer_product (hn : 0 < n) (p q : ℕ) (P Q : Poly n)
    (hp : P.IsHomogeneous p) (hq : Q.IsHomogeneous q)
    (hP : lap P = 0) (hQ : lap Q = 0) :
    ∃ H : ℕ → Poly n,
      (∀ l ≤ min p q, (H l).IsHomogeneous (p+q-2*l) ∧ lap (H l) = 0) ∧
      P * Q = ∑ l ∈ Finset.range (min p q + 1), radiusSq n ^ l * H l :=
  exists_fischer_of_iter_lap_eq_zero hn _ _ _ (hp.mul hq) (by omega)
    (iter_lap_product_eq_zero p q P Q hp hq hP hQ)

/-- Every homogeneous polynomial of degree zero or one has zero Laplacian. -/
theorem lap_low_degree (P : Poly n) {d : ℕ} (hP : P.IsHomogeneous d) (hd : d ≤ 1) :
    lap P = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have h : (pderiv i P).IsHomogeneous 0 := by
    simpa only [show d-1 = 0 by omega] using hP.pderiv (i := i)
  obtain hc := totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous _).mpr h)
  rw [hc, pderiv_C]

/-- Existence in the classical homogeneous harmonic decomposition
`P = Σ |x|^(2l) H_(d-2l)` (Stein–Weiss, Chapter IV, Theorem 2.1). -/
theorem exists_fischer (hn : 0 < n) (P : Poly n) {d : ℕ} (hP : P.IsHomogeneous d) :
    ∃ H : ℕ → Poly n, (∀ l ≤ d/2, (H l).IsHomogeneous (d-2*l) ∧ lap (H l) = 0) ∧
      P = ∑ l ∈ Finset.range (d/2+1), radiusSq n ^ l * H l := by
  apply exists_fischer_of_iter_lap_eq_zero hn _ _ _ hP (by omega)
  rw [Function.iterate_succ_apply']
  exact lap_low_degree _ (iter_lap_homogeneous _ hP _) (by omega)

/-- Polynomial numerator of the gradient product after extracting
`|x|^(-n-2q)` and applying Euler's identity to the interior homogeneous polynomial. -/
def gradientNumerator (p q : ℕ) (P Q : Poly n) : Poly n :=
  C ((p : ℂ) * (2 - n - 2*q)) * (P*Q) + radiusSq n * gradDot P Q

private theorem radiusSq_mul_lap_term (k l : ℕ) (H : Poly n)
    (hh : H.IsHomogeneous k) (hH : lap H = 0) :
    radiusSq n * lap (radiusSq n ^ l * H) =
      C (2 * (l : ℂ) * (2*(k : ℂ) + 2*l + n - 2)) * (radiusSq n ^ l * H) := by
  cases l with
  | zero => simp [hH]
  | succ l =>
    rw [lap_radiusSq_pow_succ_mul H hh hH l]
    simp only [Nat.cast_succ, map_mul, map_add, map_sub, map_natCast, map_ofNat, map_one]
    ring

/-- Algebraic content of the gradient decomposition in Section 2, equation
`graddec`, before the two endpoint cancellations. -/
theorem gradientNumerator_expansion (hn : 0 < n) (p q : ℕ) (P Q : Poly n)
    (hp : P.IsHomogeneous p) (hq : Q.IsHomogeneous q) (hP : lap P = 0) (hQ : lap Q = 0) :
    ∃ H : ℕ → Poly n, (∀ l ≤ min p q, (H l).IsHomogeneous (p+q-2*l) ∧ lap (H l) = 0) ∧
      gradientNumerator p q P Q =
        ∑ l ∈ Finset.range (min p q + 1),
          C (-((p : ℂ)-l) * (n-2+2*(q : ℂ)-2*l)) * (radiusSq n ^ l * H l) := by
  obtain ⟨H, hHarm, hsum⟩ := exists_fischer_product hn p q P Q hp hq hP hQ
  refine ⟨H, hHarm, ?_⟩
  have hprod : 2 * gradDot P Q = lap (P*Q) := by simp [lap_mul, hP, hQ]
  have hlap (s : Finset ℕ) (F : ℕ → Poly n) :
      lap (∑ l ∈ s, F l) = ∑ l ∈ s, lap (F l) := by
    simp only [lap, map_sum]; exact Finset.sum_comm
  apply mul_left_cancel₀ (a := (2 : Poly n)) (by exact_mod_cast (two_ne_zero : (2:ℂ) ≠ 0))
  unfold gradientNumerator
  rw [mul_add, ← mul_assoc 2, mul_left_comm 2 (radiusSq n), hprod, hsum, hlap]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  have hle : l ≤ min p q := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
  obtain ⟨hHl, hHz⟩ := hHarm l hle
  rw [radiusSq_mul_lap_term _ _ _ hHl hHz]
  simp only [map_mul, map_neg, map_sub, map_add, map_natCast, map_ofNat]
  have hd : 2*l ≤ p+q := by omega
  rw [Nat.cast_sub hd, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- The upper endpoint vanishes when `l=p`, and the planar endpoint also vanishes when `l=q`. -/
theorem gradientCoefficient_eq_zero_iff {n p q l : ℕ} (hn : 2 ≤ n) (hl : l ≤ min p q) :
    -((p : ℂ)-l) * ((n : ℂ)-2+2*(q : ℂ)-2*l) = 0 ↔ l = p ∨ (n = 2 ∧ l = q) := by
  have hq : l ≤ q := by omega
  have hfac : (n : ℂ)-2+2*(q : ℂ)-2*l = ((n-2 + 2*(q-l) : ℕ) : ℂ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hn, Nat.cast_sub hq, Nat.cast_ofNat]
    ring
  rw [hfac, mul_eq_zero, neg_eq_zero, sub_eq_zero, Nat.cast_inj, Nat.cast_eq_zero]
  omega

end Runcorn.Polynomial
