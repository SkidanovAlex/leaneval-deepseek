import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.ELRig.cert

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2

/-- The fifth iterate of `T` is the fractional part of `-32 θ` on the `α₂`-window: the
endpoints `α₂ = 404/1023` and `β₀' = 414113/1047552` satisfy `3/8 < α₂ < β₀' < 13/32`,
so on `(α₂, β₀']` we have `-13 < -32 θ < -12` and `T^[5] θ = fract (-32 θ) = -32 θ + 13`. -/
theorem T5_window {θ : ℝ} (hlo : Work.EL.alpha2 < θ) (hhi : θ ≤ Work.ELNest.beta0') :
    Work.EL.T^[5] θ = Work.EL.alpha1 - 32 * (θ - Work.EL.alpha2) := by
  -- `α₁ + 32 α₂ = 371/1023 + 32·404/1023 = 13299/1023 = 13`
  have hkey : Work.EL.alpha1 + 32 * Work.EL.alpha2 = 13 := by
    rw [Work.EL.alpha1, Work.EL.alpha2]; norm_num
  -- the window `(α₂, β₀']` sits strictly inside `(3/8, 13/32)`
  have h_a : (3 : ℝ) / 8 < Work.EL.alpha2 := by rw [Work.EL.alpha2]; norm_num
  have h_b : Work.ELNest.beta0' < 13 / 32 := by rw [Work.ELNest.beta0']; norm_num
  have h_low : (3 : ℝ) / 8 < θ := lt_trans h_a hlo
  have h_high : θ < 13 / 32 := lt_of_le_of_lt hhi h_b
  have h32hi : -32 * θ < -12 := by linarith
  have h32lo : -13 < -32 * θ := by linarith
  -- the iterate `T^[5] θ = fract (-32 θ)`
  have hT : Work.EL.T^[5] θ = Int.fract (-32 * θ) := by
    have h := Work.ELNest.T_iterate_succ 4 θ
    have : (((-2 : ℝ)) ^ (4 + 1)) * θ = -32 * θ := by norm_num
    rw [this] at h
    simpa using h
  rw [hT, Int.fract_eq_iff]
  refine ⟨?_, ?_, ⟨-13, ?_⟩⟩
  · -- `α₁ - 32 (θ - α₂) = -32 θ + 13 ∈ (0,1)`
    have : Work.EL.alpha1 - 32 * (θ - Work.EL.alpha2) = -32 * θ + 13 := by linarith [hkey]
    rw [this]; linarith
  · have : Work.EL.alpha1 - 32 * (θ - Work.EL.alpha2) = -32 * θ + 13 := by linarith [hkey]
    rw [this]; linarith
  · -- `-32 θ - (α₁ - 32 (θ - α₂)) = -(α₁ + 32 α₂) = -13 ∈ ℤ`
    push_cast
    linarith [hkey]

end Work.GATE2
