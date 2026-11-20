module

public import Runcorn.Definitions
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Continuity and integrability of the harmonic tests on compact subannuli -/
@[expose] public section

noncomputable section
open MeasureTheory Set

namespace Runcorn

theorem continuousOn_test {n : ℕ} {lo hi : ℝ} {u v f : Space n → ℂ}
    (hf : ContinuousOn f (shell lo hi)) (huv : Admissible lo hi u v) :
    ContinuousOn (fun x => f x * gradDot u v x) (shell lo hi) := by
  apply hf.mul
  intro x hx
  apply ContinuousAt.continuousWithinAt
  unfold gradDot
  apply tendsto_finsetSum
  intro i _
  have hu := (huv.1 x hx.2).1.continuousAt_fderiv (by decide)
  have hv := (huv.2.1 x hx.1).1.continuousAt_fderiv (by decide)
  exact (hu.clm_apply continuousAt_const).mul (hv.clm_apply continuousAt_const)

theorem isCompact_annulus {n : ℕ} (a b : ℝ) : IsCompact (annulus (n := n) a b) := by
  apply (isCompact_closedBall (0 : Space n) b).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx
    simpa using hx.2

theorem integrableOn_test {n : ℕ} {lo hi a b : ℝ} {f u v : Space n → ℂ}
    (hf : ContinuousOn f (shell lo hi)) (huv : Admissible lo hi u v)
    (ha : lo < a) (hb : b < hi) :
    IntegrableOn (fun x => f x * gradDot u v x) (annulus a b) := by
  exact ((continuousOn_test hf huv).mono fun _ hx =>
    ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩).integrableOn_compact (isCompact_annulus a b)

end Runcorn
