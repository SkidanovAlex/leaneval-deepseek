import Mathlib
import Submission.Work.WilG4a.CD.Defs

namespace Work.WilG4a.CD

theorem iota_pull (p : ℕ) (z : Fin (p + 1) → ℝ) (δ y : ℝ) :
    (Fin.snoc (Fin.snoc z δ) y) ∘ (iotaInfl p) = Fin.snoc (Fin.init z) y := by
  funext j
  induction j using Fin.lastCases with
  | last => simp only [Function.comp_apply, iotaInfl, Fin.snoc_last]
  | cast i => simp only [Function.comp_apply, iotaInfl, Fin.snoc_castSucc, Fin.init]

end Work.WilG4a.CD
