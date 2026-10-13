import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Submission.Work.FTS.EllipticEst.TT.logCutDefs
import Submission.Work.ChiExplicit.chi_contDiff
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

/-- `logChi n` is `C^∞` (genuine smoothness, `Work.Stability.smoothOrder = ((⊤ : ℕ∞) : ℕ∞ω)`,
NOT analyticity) on the open half-line `(0,∞)`: it is the composition of the globally `C^∞` bump
`Work.ChiExplicit.chi` with `z ↦ Real.log z / Real.log ((n:ℝ)+2)`, which is smooth on `(0,∞)`
and whose denominator `log ((n:ℝ)+2)` is positive because `(n:ℝ)+2 ≥ 2 > 1`. -/
theorem logChi_contDiffOn (n : ℕ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Work.FTS.EllipticEst.TT.logChi n) (Set.Ioi 0) := by
  -- The rescaling `g z = log z / log ((n:ℝ)+2)` is smooth on `(0,∞)`: `Real.log` is smooth off
  -- `0`, and dividing by the *constant* `log ((n:ℝ)+2)` preserves smoothness.
  have hg : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Real.log z / Real.log ((n : ℝ) + 2)) (Set.Ioi 0) :=
    (Real.contDiffOn_log.mono (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx)).div_const _
  -- `chi` is globally `C^∞`, hence `C^∞` on every set; compose with `g`.
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (Work.ChiExplicit.chi ∘ fun z : ℝ => Real.log z / Real.log ((n : ℝ) + 2))
      (Set.Ioi 0) :=
    (Work.ChiExplicit.chi_contDiff (⊤ : ℕ∞)).comp_contDiffOn hg
  -- Unfold `logChi` and `Function.comp`.
  exact hcomp.congr (fun z _ => rfl)

end Work.FTS.EllipticEst.TT
