import Mathlib
import Submission.Work.HP.badclass.BadDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
noncomputable section

open MvPolynomial Finset

namespace Work.HP.badclass

/-- The number of torus points collinear with a fixed `x` is at most `p`. -/
theorem resonant_card (n p : ℕ) [NeZero p] (x : Fin (n + 1) → ZMod p) :
    ((Work.HP.torFinset n p).filter (fun y => ∃ z : ZMod p, y = z • x)).card ≤ p := by
  classical
  calc ((Work.HP.torFinset n p).filter (fun y => ∃ z : ZMod p, y = z • x)).card
      ≤ ((Finset.univ : Finset (ZMod p)).image (fun z => z • x)).card := by
        apply Finset.card_le_card
        intro y hy
        rw [Finset.mem_filter] at hy
        obtain ⟨z, rfl⟩ := hy.2
        exact Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩
    _ ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_image_le
    _ = p := by simp [ZMod.card]

end Work.HP.badclass
