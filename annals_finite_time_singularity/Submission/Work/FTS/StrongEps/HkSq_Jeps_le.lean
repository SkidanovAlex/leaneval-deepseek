import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Commute
import Submission.Work.FTS.StrongEps.Dth_Jeps
import Submission.Work.FTS.StrongEps.wtE_shift_le
import Submission.Work.FTS.StrongEps.wtG_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.Pointwise
import Submission.Work.FTS.StrongEps.HkSqAux.HkIntegrand_Jeps_le_integral
import Submission.Work.FTS.StrongEps.HkSqAux.LogCoord
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.integral_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_pair
import Submission.Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_slice
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad
import Submission.Work.FTS.StrongEps.HkSqAux.Chain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-- **E1: the log-coordinate mollifier `J_ε` is bounded on the weighted spaces `ℋ^k` up to a
factor `e^{Cε}`.** -/
theorem HkSq_Jeps_le (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ f : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) →
        Work.Spaces.HkMem α k f → Work.Spaces.HkMem α k (Jeps ρ ε f) →
          Work.Spaces.HkSq α k (Jeps ρ ε f)
            ≤ Real.exp (C * ε) * Work.Spaces.HkSq α k f := by
  obtain ⟨cη, hcηpos, hWη0⟩ := HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγpos, hWγ0⟩ := HkSqAux.Wt_shift_le
  obtain ⟨δ, hδpos, hJac0⟩ := HkSqAux.logJac_shift_le
  refine ⟨4 * max cη cγ + 2 * δ, by positivity, ?_⟩
  intro α hα k ε hε _ f hf hF hFJ
  have hc0 : 0 ≤ max cη cγ := le_of_lt (lt_of_lt_of_le hcηpos (le_max_left _ _))
  have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
          * (Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2)) := by
    intro z θ hz hθ p
    refine (hWη0 z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact div_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)
  have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ
        ≤ Real.exp (max cη cγ * (|p.1| + |p.2|))
          * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2) := by
    intro z θ hz hθ p
    exact (hWγ0 α hα z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)))
  have hmain := HkSqAux.ofReal_HkSq_Jeps_le ρ hρ hα hε hf hF hFJ (c := max cη cγ) (δ := δ)
    hc0 (le_of_lt hδpos) hWη hWγ (fun s ζ p₁ p₂ => hJac0 s ζ p₁ p₂)
  have hconv : ENNReal.ofReal (Real.exp ((4 * max cη cγ + 2 * δ) * ε)
        * Work.Spaces.HkSq α k f)
      = ENNReal.ofReal (Real.exp ((4 * max cη cγ + 2 * δ) * ε))
        * ENNReal.ofReal (Work.Spaces.HkSq α k f) :=
    ENNReal.ofReal_mul (Real.exp_pos _).le
  rw [← hconv] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.exp_pos _).le (Work.Spaces.HkSq_nonneg α k f))).mp hmain

end Work.FTS.StrongEps
