import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.FTS_RegExport.RXT.C2Assemble
import Submission.Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

theorem SlotJetsTendsto {α : ℝ} {Ξ : ℕ → ℝ → ℝ → ℝ} {Ξlim : ℝ → ℝ → ℝ}
    (hΞ : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry (Ξ n)) Work.FTS.EllipticEst.Q0)
    (hΞlim : ContDiffOn ℝ 3 (Function.uncurry Ξlim) Work.FTS.EllipticEst.Q0)
    (hconv : ∀ (b a : ℕ), a + b ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (Ξ n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a Ξlim z θ))) :
    ∀ (j i : ℕ), j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
            (fun z θ => Work.Construction.Rop α (Ξ n) z θ) z θ) Filter.atTop
          (nhds (Work.Spaces.mixed j i (fun z θ => Work.Construction.Rop α Ξlim z θ) z θ)) ∧
        Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
            (fun z θ => Work.Construction.Vop (Ξ n) z θ) z θ) Filter.atTop
          (nhds (Work.Spaces.mixed j i (fun z θ => Work.Construction.Vop Ξlim z θ) z θ)) ∧
        Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
            (fun z θ => Work.Construction.Uop α (Ξ n) z θ / Real.sin (2 * θ)) z θ) Filter.atTop
          (nhds (Work.Spaces.mixed j i
            (fun z θ => Work.Construction.Uop α Ξlim z θ / Real.sin (2 * θ)) z θ))) :=
  -- REPOINTED: the same statement is proved sorry-free in `RXT.Slots`
  -- (`RXT/Slots/v2_SlotJetsTendsto.lean`), which is the twin this stub was carved from.
  Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto hΞ hΞlim hconv

end Work.FTS_RegExport.RXT
