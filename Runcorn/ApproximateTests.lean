module

public import Runcorn.PairingLimit
public import Runcorn.TestRegularity
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Passing from finite mode tests to harmonic tests

Approximate each gradient separately in L² on the compact annulus. With one
test function held fixed, its continuous coordinate derivatives are bounded.
Multiplication of the L² weight by any of them leaves an L² weight. The
continuous bilinear pairing therefore permits passage to the limit.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Runcorn

/-- One real Cartesian partial derivative of the complex function u. -/
abbrev coordDerivative {n : ℕ} (u : Space n → ℂ) (i : Fin n) (x : Space n) : ℂ :=
  fderiv ℝ u x (EuclideanSpace.single i 1)

private theorem cont_memLp_annulus {n : ℕ} {a b : ℝ} {g : Space n → ℂ}
    (hc : ContinuousOn g (annulus a b)) : MemLp g 2 (volume.restrict (annulus a b)) := by
  have hK := isCompact_annulus (n := n) a b
  exact (memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable hK.measurableSet)).mpr
    ((hc.norm.pow 2).integrableOn_compact hK)

private theorem cont_memLp_top_annulus {n : ℕ} {a b : ℝ} {g : Space n → ℂ}
    (hc : ContinuousOn g (annulus a b)) : MemLp g ⊤ (volume.restrict (annulus a b)) := by
  have hK := isCompact_annulus (n := n) a b
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  exact memLp_top_of_bound (hc.aestronglyMeasurable hK.measurableSet) C
    ((ae_restrict_mem hK.measurableSet).mono (fun x hx ↦ hC x hx))

private theorem integral_gradDot_eq_sum {n : ℕ} {a b : ℝ} {f u v : Space n → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulus a b)))
    (hu : ∀ i, ContinuousOn (coordDerivative u i) (annulus a b))
    (hv : ∀ i, ContinuousOn (coordDerivative v i) (annulus a b)) :
    (∫ x in annulus a b, f x * gradDot u v x) =
      ∑ i : Fin n, ∫ x in annulus a b,
        coordDerivative u i x * (f x * coordDerivative v i x) := by
  have hin (i : Fin n) : IntegrableOn (fun x ↦
      coordDerivative u i x * (f x * coordDerivative v i x)) (annulus a b) := by
    have hweight : MemLp (fun x ↦ f x * coordDerivative v i x) 2 (volume.restrict (annulus a b)) :=
      hf.mul (cont_memLp_top_annulus (hv i))
    exact (cont_memLp_annulus (hu i)).integrable_mul hweight
  rw [← integral_finsetSum _ (fun i _ ↦ hin i)]
  apply setIntegral_congr_fun (isCompact_annulus a b).measurableSet
  intro x _
  unfold gradDot
  dsimp only
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _

private theorem annular_test_tendsto_left {n : ℕ} {a b : ℝ} {f u v : Space n → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulus a b))) (U : ℕ → Space n → ℂ)
    (hU : ∀ N i, ContinuousOn (coordDerivative (U N) i) (annulus a b))
    (hu : ∀ i, ContinuousOn (coordDerivative u i) (annulus a b))
    (hv : ∀ i, ContinuousOn (coordDerivative v i) (annulus a b))
    (hUlim : ∀ i, Tendsto (fun N ↦ eLpNorm
      (fun x ↦ coordDerivative (U N) i x - coordDerivative u i x) 2
      (volume.restrict (annulus a b))) atTop (𝓝 0)) :
    Tendsto (fun N ↦ ∫ x in annulus a b, f x * gradDot (U N) v x) atTop
      (𝓝 (∫ x in annulus a b, f x * gradDot u v x)) := by
  simp_rw [integral_gradDot_eq_sum hf (hU _) hv, integral_gradDot_eq_sum hf hu hv]
  apply tendsto_finsetSum
  intro i _
  have hweight : MemLp (fun x ↦ f x * coordDerivative v i x) 2 (volume.restrict (annulus a b)) :=
    hf.mul (cont_memLp_top_annulus (hv i))
  exact integral_tendsto_of_L2_limit (fun N ↦ cont_memLp_annulus (hU N i))
    (cont_memLp_annulus (hu i)) hweight (hUlim i)

/-- Derivative convergence for the two finite-mode approximants can be used successively.
In particular the two convergence rates are independent. -/
theorem annular_test_zero_of_gradient_approximations {n : ℕ} {a b : ℝ} {f u v : Space n → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulus a b))) (U V : ℕ → Space n → ℂ)
    (hU : ∀ N i, ContinuousOn (coordDerivative (U N) i) (annulus a b))
    (hV : ∀ N i, ContinuousOn (coordDerivative (V N) i) (annulus a b))
    (hu : ∀ i, ContinuousOn (coordDerivative u i) (annulus a b))
    (hv : ∀ i, ContinuousOn (coordDerivative v i) (annulus a b))
    (hUlim : ∀ i, Tendsto (fun N ↦ eLpNorm
      (fun x ↦ coordDerivative (U N) i x - coordDerivative u i x) 2
      (volume.restrict (annulus a b))) atTop (𝓝 0))
    (hVlim : ∀ i, Tendsto (fun N ↦ eLpNorm
      (fun x ↦ coordDerivative (V N) i x - coordDerivative v i x) 2
      (volume.restrict (annulus a b))) atTop (𝓝 0))
    (hzero : ∀ N M, (∫ x in annulus a b, f x * gradDot (U N) (V M) x) = 0) :
    (∫ x in annulus a b, f x * gradDot u v x) = 0 := by
  have hcomm (g h : Space n → ℂ) (x : Space n) : gradDot g h x = gradDot h g x :=
    Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)
  have hz (M : ℕ) : (∫ x in annulus a b, f x * gradDot u (V M) x) = 0 := by
    apply tendsto_nhds_unique (annular_test_tendsto_left hf U hU hu (hV M) hUlim)
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0))
  simp_rw [hcomm u v]
  apply tendsto_nhds_unique (annular_test_tendsto_left hf V hV hv hu hVlim)
  simpa only [hcomm (V _) u, hz] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ ↦ (0 : ℂ)) atTop (𝓝 0))

end Runcorn
