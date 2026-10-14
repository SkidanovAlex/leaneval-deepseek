import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.Glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Reindexing -/

/-- A `LimSeq4` is stable under composition with any index map tending to infinity. -/
theorem limSeq4_comp {α : ℝ} {fn : ℕ → Fn} {f : Fn} (hL : LimSeq4 α fn f) {σ : ℕ → ℕ}
    (hσ : Tendsto σ atTop atTop) : LimSeq4 α (fun n => fn (σ n)) f where
  classC n := hL.classC (σ n)
  bound := by
    obtain ⟨B, hB⟩ := hL.bound
    exact ⟨B, fun n => hB (σ n)⟩
  c4 := hL.c4
  conv j i hji z θ hz := (hL.conv j i hji z θ hz).comp hσ

/-! ## The two obligations -/





/-! ## The reduction -/



end Work.FTS_EllLimOK
