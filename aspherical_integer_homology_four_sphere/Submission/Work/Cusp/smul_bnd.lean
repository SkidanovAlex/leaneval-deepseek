import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- `p = ‖p‖∞ • bnd p`: the radial projection `bnd` recovers `p` from its sup norm and its
direction.  At `p = 0` both sides vanish (`bnd 0 = 0` because `0⁻¹ = 0` in `ℝ`), and otherwise
`nrm p * (nrm p)⁻¹ = 1`. -/
theorem smul_bnd (p : E2) : nrm p • bnd p = p := by
  rw [bnd, smul_smul]
  rcases eq_or_ne (nrm p) 0 with h | h
  · -- `nrm p = 0` forces `p = 0`, since `nrm p` dominates both coordinates.
    have hp : p = 0 := by
      have h0 : p 0 = 0 := by
        have : |p 0| = 0 := le_antisymm (by rw [← h]; exact le_max_left _ _) (abs_nonneg _)
        exact abs_eq_zero.mp this
      have h1 : p 1 = 0 := by
        have : |p 1| = 0 := le_antisymm (by rw [← h]; exact le_max_right _ _) (abs_nonneg _)
        exact abs_eq_zero.mp this
      ext i
      fin_cases i <;> simp [h0, h1]
    subst hp
    simp [h]
  · rw [mul_inv_cancel₀ h, one_smul]

end Work.Cusp
