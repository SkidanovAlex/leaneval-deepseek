import Mathlib
import Submission.Work.ELNest.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELNest

/-- The two level-`n` angles of the `z₁`-nest both stay in their expected windows:
`βₙ ∈ (0, α₁)` and `βₙ' ∈ (α₂, β₀']`. -/
theorem bAng_range (n : ℕ) :
    (0 < Work.ELNest.bAng n ∧ Work.ELNest.bAng n < Work.ELNest.alpha1) ∧
    (Work.ELNest.alpha2 < Work.ELNest.bAng' n ∧ Work.ELNest.bAng' n ≤ Work.ELNest.beta0') := by
  have hp1 : (1 : ℝ) ≤ (1024 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hp0 : (0 : ℝ) < (1024 : ℝ) ^ n := lt_of_lt_of_le (by norm_num) hp1
  have hd : 0 < alpha1 - beta0 := by norm_num [alpha1, beta0]
  have he : 0 < beta0' - alpha2 := by norm_num [alpha2, beta0']
  have hd0 : 0 ≤ alpha1 - beta0 := le_of_lt hd
  have he0 : 0 ≤ beta0' - alpha2 := le_of_lt he
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [bAng]
    rw [sub_pos]
    exact lt_of_le_of_lt (div_le_self hd0 hp1) (sub_lt_self _ (by norm_num [beta0]))
  · rw [bAng]
    exact sub_lt_self _ (div_pos hd hp0)
  · rw [bAng']
    exact lt_add_of_pos_right _ (div_pos he hp0)
  · rw [bAng']
    have h := add_le_add_left (div_le_self he0 hp1) alpha2
    linarith [h]

end Work.ELNest
