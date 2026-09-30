import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

theorem uPerim_corner_approx : ∀ ε > 0, ∃ δ > 0, ∀ q : E2, nrm q = 1 → |q 0 - 1| < δ → |q 1 - 1| < δ → uPerim q < ε ∨ 1 - ε < uPerim q := by
  intro ε hε
  refine ⟨min 1 (8 * ε), ?_, ?_⟩
  · exact lt_min one_pos (by linarith)
  · intro q _ h0 h1
    have hδle : min 1 (8 * ε) ≤ 8 * ε := min_le_right _ _
    have hδle1 : min 1 (8 * ε) ≤ 1 := min_le_left _ _
    have hq0lo : 1 - min 1 (8 * ε) < q 0 := by
      have := (abs_lt.mp h0).1; linarith
    have hq1lo : 1 - min 1 (8 * ε) < q 1 := by
      have := (abs_lt.mp h1).1; linarith
    unfold uPerim
    split_ifs with hA hB hC
    · left
      have : (1 - q 1) / 8 < min 1 (8 * ε) / 8 := by linarith
      have h2 : min 1 (8 * ε) / 8 ≤ ε := by linarith
      linarith
    · exfalso
      have := (abs_lt.mp h1).1
      rw [hB] at this
      linarith
    · exfalso
      have := (abs_lt.mp h0).1
      rw [hC] at this
      linarith
    · right
      have h2 : (7 + q 0) / 8 > 1 - ε := by linarith
      linarith

end Work.Cusp
