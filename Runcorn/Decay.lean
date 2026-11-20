module

public import Runcorn.SpecialPair
public import Runcorn.Definitions
public import Mathlib.Topology.Algebra.Order.Field

/-! # Decay of the exterior test in Lemma 4

The positive radial bound after taking norms has homogeneity `s + q`.
For the Kelvin transform of a degree-`q` polynomial this is `2 - n - q`.
-/

@[expose] public section
noncomputable section
open Filter Topology

namespace Runcorn

/-- A power of a bounded linear form times an integer power of the radius
vanishes at infinity when its total homogeneity is negative. -/
theorem tendsto_radial_linear_power {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (s : ℤ) (q : ℕ) (h : s + q < 0) :
    Tendsto (fun x : E => ((‖x‖ ^ s : ℝ) : ℂ) * (L x) ^ q)
      (comap (fun x : E => ‖x‖) atTop) (𝓝 0) := by
  have hr : Tendsto (fun x : E => ‖x‖) (comap (fun x : E => ‖x‖) atTop) atTop := tendsto_comap
  have hlimit : Tendsto (fun x : E => ‖L‖ ^ q * ‖x‖ ^ (s + q))
      (comap (fun x : E => ‖x‖) atTop) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ‖L‖ ^ q)).mul ((tendsto_zpow_atTop_zero h).comp hr)
  apply squeeze_zero_norm' _ hlimit
  filter_upwards [hr.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (zpow_nonneg hx.le _)]
  calc
    ‖x‖ ^ s * ‖L x‖ ^ q ≤ ‖x‖ ^ s * (‖L‖ * ‖x‖) ^ q :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm x) _) (zpow_nonneg hx.le _)
    _ = ‖L‖ ^ q * ‖x‖ ^ (s + q) := by
      rw [mul_pow, zpow_add₀ hx.ne', zpow_natCast]
      ring

/-- The decay condition in Lemma 4, including the excluded planar monopole. -/
theorem specialPair_vanishes_at_infinity {n q : ℕ} (hn : 2 ≤ n)
    (hq : n = 2 → 1 ≤ q) (ζ : Fin n → ℂ) :
    Tendsto (fun x : Space n => ((‖x‖ ^ (2 - (n : ℤ) - 2*q) : ℝ) : ℂ) *
      (SpecialPair.form ζ x) ^ q) (comap (fun x : Space n => ‖x‖) atTop) (𝓝 0) := by
  apply tendsto_radial_linear_power
  omega

end Runcorn
