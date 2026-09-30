import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

theorem bnd_mem {p : E2} (hp : p ∈ Sq) : bnd p ∈ Sq := by
  obtain ⟨h0, h1⟩ := hp
  -- `nrm p = max |p 0| |p 1| ≥ 0`
  have hn0 : 0 ≤ nrm p := le_trans (abs_nonneg _) (le_max_left _ _)
  -- the two coordinates of `bnd p = (nrm p)⁻¹ • p`
  have hb0 : bnd p 0 = (nrm p)⁻¹ * p 0 := by simp [bnd]
  have hb1 : bnd p 1 = (nrm p)⁻¹ * p 1 := by simp [bnd]
  constructor
  · rw [hb0]
    rcases eq_or_ne (nrm p) 0 with h | h
    · simp [h]
    · rw [abs_mul, abs_of_pos (inv_pos.mpr (lt_of_le_of_ne hn0 (Ne.symm h)))]
      calc (nrm p)⁻¹ * |p 0| ≤ (nrm p)⁻¹ * nrm p :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (inv_nonneg.mpr hn0)
        _ = 1 := inv_mul_cancel₀ h
  · rw [hb1]
    rcases eq_or_ne (nrm p) 0 with h | h
    · simp [h]
    · rw [abs_mul, abs_of_pos (inv_pos.mpr (lt_of_le_of_ne hn0 (Ne.symm h)))]
      calc (nrm p)⁻¹ * |p 1| ≤ (nrm p)⁻¹ * nrm p :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr hn0)
        _ = 1 := inv_mul_cancel₀ h

end Work.Cusp
