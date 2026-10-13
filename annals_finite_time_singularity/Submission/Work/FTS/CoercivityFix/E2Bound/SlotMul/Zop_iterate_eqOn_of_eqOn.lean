import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.MixedMulDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.E2Bound.SlotMul

/-- `Zop` is the one-dimensional operator `u ↦ (z ↦ z·u'(z))` (see
`Work.Spaces.Zop`).  Equality of two functions on an *open* set propagates to their
derivatives on that set (`Set.EqOn.deriv`), hence to every iterate of `Zop`. -/
theorem Zop_iterate_eqOn_of_eqOn (b : ℕ) {s : Set ℝ} (hs : IsOpen s) {f g : ℝ → ℝ}
    (h : Set.EqOn f g s) :
    Set.EqOn (Work.Spaces.Zop^[b] f) (Work.Spaces.Zop^[b] g) s := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    intro z hz
    simp only [Function.iterate_succ', Function.comp_apply, Work.Spaces.Zop]
    rw [ih.deriv hs hz]

end Work.FTS.CoercivityFix.E2Bound.SlotMul
