module

public import Runcorn.MomentNecessity
public import Runcorn.PolarMeasure
public import Runcorn.ProductSeries

/-! # Necessity in Theorem 2

The coefficients are the normalized spherical integrals in (1.4). Polar
transport and the orthogonal angular expansion give convergence in the L²
norm of the closed annulus. The null-vector test proof gives membership of
each coefficient in the paper's finite-moment subspace.
-/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Runcorn

theorem fixedTests_hasMomentExpansion {n : ℕ} (hn : 2 ≤ n) {lo hi a b : ℝ}
    (hlo : 0 < lo) (ha : lo < a) (Y : AngularFamily n) (hY : IsAngularBasis Y)
    {f : Space n → ℂ} (hf : MemLp f 2 (volume.restrict (annulus a b)))
    (ht : FixedTests lo hi a b f) : HasMomentExpansion a b Y f := by
  let μ := (radialMeasure n a b).prod (surfaceMeasure n)
  let F := f ∘ polarMap n
  let g : Coefficients n := fun k j ↦ productCoefficient Y F ⟨k,j⟩
  have hr := hlo.trans ha
  have hF : MemLp F 2 μ := (memLp_polar_iff hn hr).mpr hf
  obtain ⟨hg, hprod, hlim⟩ := product_angular_expansion hn Y hY F hF
  have hpart (N : ℕ) :
      (partialExpansion Y g N ∘ polarMap n) =ᵐ[μ] productPartial Y F N := by
    filter_upwards [ae_polar_positive hr] with p hp
    exact partialExpansion_polar Y g N p.1 hp p.2
  have hamb (N : ℕ) : MemLp (partialExpansion Y g N) 2 (volume.restrict (annulus a b)) :=
    (memLp_polar_iff hn hr).mp ((memLp_congr_ae (hpart N)).mpr (hprod N))
  refine ⟨g, ?_, hamb, ?_⟩
  · intro k j
    refine ⟨hg ⟨k,j⟩, ?_⟩
    intro m hm
    exact fixedTests_normalized_moments hn hlo ha hf ht Y hY k j m hm
  · refine hlim.congr (fun N ↦ ?_)
    rw [← eLpNorm_polar (f := fun x ↦ partialExpansion Y g N x - f x) hn hr ((hamb N).sub hf).aestronglyMeasurable]
    apply eLpNorm_congr_ae
    filter_upwards [hpart N] with p hp
    exact congrArg (fun z ↦ z - F p) hp.symm

end Runcorn
