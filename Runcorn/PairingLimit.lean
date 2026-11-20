module

public import Mathlib.MeasureTheory.Function.L2Space

/-! # Continuous complex bilinear testing on L² -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace Runcorn

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- L² convergence preserves the bilinear integral against a fixed L² weight. -/
theorem integral_tendsto_of_L2_limit {F : ℕ → X → ℂ} {f w : X → ℂ}
    (hF : ∀ N, MemLp (F N) 2 μ) (hf : MemLp f 2 μ) (hw : MemLp w 2 μ)
    (ht : Tendsto (fun N ↦ eLpNorm (fun x ↦ F N x - f x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun N ↦ ∫ x, F N x * w x ∂μ) atTop (𝓝 (∫ x, f x * w x ∂μ)) := by
  have hconj : MemLp (fun x ↦ conj (w x)) 2 μ :=
    hw.continuousLinearMap_comp Complex.conjCLE.toContinuousLinearMap
  let W := hconj.toLp (fun x ↦ conj (w x))
  have hpair {g : X → ℂ} (hg : MemLp g 2 μ) :
      inner ℂ W (hg.toLp g) = ∫ x, g x * w x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp, hconj.coeFn_toLp] with x hx hwx
    simp [RCLike.inner_apply, W, hx, hwx]
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF f hf).mpr ht
  simpa only [Function.comp_def, innerSL_apply_apply, hpair] using
    (innerSL ℂ W).continuous.continuousAt.tendsto.comp h

/-- A fixed bilinear L² test which annihilates every approximant annihilates its L² limit. -/
theorem integral_zero_of_L2_limit {F : ℕ → X → ℂ} {f w : X → ℂ}
    (hF : ∀ N, MemLp (F N) 2 μ) (hf : MemLp f 2 μ) (hw : MemLp w 2 μ)
    (ht : Tendsto (fun N ↦ eLpNorm (fun x ↦ F N x - f x) 2 μ) atTop (𝓝 0))
    (hz : ∀ N, (∫ x, F N x * w x ∂μ) = 0) : (∫ x, f x * w x ∂μ) = 0 := by
  apply tendsto_nhds_unique (integral_tendsto_of_L2_limit hF hf hw ht)
  simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0))

end Runcorn
