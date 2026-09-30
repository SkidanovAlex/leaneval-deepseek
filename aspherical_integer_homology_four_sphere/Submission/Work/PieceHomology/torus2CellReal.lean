import Mathlib
import Submission.Work.PieceHomology.Torus2Chi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.PieceHomology

theorem torus2CellReal :
    (∀ (x : Fin 2 → AddCircle (1 : ℝ)) (h1 : 0 < Work.PieceHomology.uy x)
        (h2 : Work.PieceHomology.uy x < Work.PieceHomology.ux x),
        Work.PieceHomology.chiT0 (Work.PieceHomology.ptT0 x h2.le) = x) ∧
    (∀ (x : Fin 2 → AddCircle (1 : ℝ)) (h1 : 0 < Work.PieceHomology.ux x)
        (h2 : Work.PieceHomology.ux x < Work.PieceHomology.uy x),
        Work.PieceHomology.chiT1 (Work.PieceHomology.ptT1 x h2.le) = x) ∧
    (∀ (x : Fin 2 → AddCircle (1 : ℝ)) (h1 : Work.PieceHomology.uy x = 0)
        (h2 : 0 < Work.PieceHomology.ux x),
        Work.PieceHomology.chiA (Work.PieceHomology.ptA x) = x) ∧
    (∀ (x : Fin 2 → AddCircle (1 : ℝ)) (h1 : Work.PieceHomology.ux x = 0)
        (h2 : 0 < Work.PieceHomology.uy x),
        Work.PieceHomology.chiB (Work.PieceHomology.ptB x) = x) ∧
    (∀ (x : Fin 2 → AddCircle (1 : ℝ)) (h1 : 0 < Work.PieceHomology.ux x)
        (h2 : Work.PieceHomology.ux x = Work.PieceHomology.uy x),
        Work.PieceHomology.chiC (Work.PieceHomology.ptC x) = x) ∧
    (∀ (x : Fin 2 → AddCircle (1 : ℝ)), Work.PieceHomology.ux x = 0 →
        Work.PieceHomology.uy x = 0 → Work.PieceHomology.chiV Work.PieceHomology.ptV = x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _ h2
    funext i; fin_cases i <;>
      simp [chiT0, tpt, ptT0, stdSimplex3, coe_ux, coe_uy]
  · intro x _ h2
    funext i; fin_cases i <;>
      simp [chiT1, tpt, ptT1, stdSimplex3, coe_ux, coe_uy]
  · intro x h1 _
    funext i; fin_cases i
    · simpa [chiA, tpt] using coe_ux x
    · simp [chiA, tpt]
      rw [← coe_uy x, h1]; simp
  · intro x h1 _
    funext i; fin_cases i
    · simp [chiB, tpt]
      rw [← coe_ux x, h1]; simp
    · simpa [chiB, tpt] using coe_uy x
  · intro x _ h2
    funext i; fin_cases i
    · simpa [chiC, tpt, ptC] using coe_ux x
    · simp [chiC, tpt, ptC]
      rw [← coe_uy x, h2]
  · intro x h1 h2
    funext i; fin_cases i
    · simp [chiV, tpt]
      rw [← coe_ux x, h1]; simp
    · simp [chiV, tpt]
      rw [← coe_uy x, h2]; simp

end Work.PieceHomology
