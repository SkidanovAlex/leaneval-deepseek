import Mathlib
import Submission.Work.Escape.Shadow

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Escape

theorem norm_shadowTd (d : ℕ) (c : ℂ) (k : ℕ) (z : ℂ) :
    ‖shadowTd d c k z‖ = ‖(Td d c)^[k] z‖ := by
  have key : ∀ k : ℕ, ∀ w : ℂ, ‖shadowTd d c k w‖ = ‖(Td d c)^[k] w‖ := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero => intro w; simp
    | one => intro w
             rw [shadowTd_one, fTd_apply, starRingEnd_apply, norm_star, Function.iterate_one]
    | more n ih _ =>
        intro w
        rw [shadowTd_add_two]
        simp only [Function.comp_apply]
        rw [ih]
        have h2 : pTd d c w = (Td d c)^[2] w := by rw [pTd_apply]; rfl
        rw [h2, Function.iterate_add_apply]
  exact key k z

end Work.Escape
