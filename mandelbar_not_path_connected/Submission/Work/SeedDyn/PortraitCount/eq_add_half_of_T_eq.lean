import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn.PortraitCount

theorem eq_add_half_of_T_eq {θ' θ'' : ℝ}
    (h' : θ' ∈ Set.Ico (0 : ℝ) 1) (h'' : θ'' ∈ Set.Ico (0 : ℝ) 1)
    (hT : Work.ELPull.T θ' = Work.ELPull.T θ'') (hne : θ' ≠ θ'') :
    θ'' = θ' + 1 / 2 ∨ θ' = θ'' + 1 / 2 := by
  simp only [Work.ELPull.T_def] at hT
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp hT
  have hz2 : 2 * (θ'' - θ') = (z : ℝ) := by linarith
  have hlt : (z : ℝ) < 2 := by linarith [h'.1, h''.2]
  have hgt : (-2 : ℝ) < (z : ℝ) := by linarith [h'.2, h''.1]
  have hzlt : z < 2 := by exact_mod_cast hlt
  have hzgt : (-2 : ℤ) < z := by exact_mod_cast hgt
  have hcases : z = -1 ∨ z = 0 ∨ z = 1 := by omega
  rcases hcases with h | h | h
  · right; rw [h] at hz2; push_cast at hz2; linarith
  · exfalso; apply hne; rw [h] at hz2; push_cast at hz2; linarith
  · left; rw [h] at hz2; push_cast at hz2; linarith

end Work.SeedDyn.PortraitCount
