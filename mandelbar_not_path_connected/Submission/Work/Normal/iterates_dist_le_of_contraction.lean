import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

theorem iterates_dist_le_of_contraction {f : ℂ → ℂ} {y : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hstep : ∀ z : ℂ, dist z y ≤ ρ → dist (f z) y ≤ (1 / 2) * dist z y) :
    ∀ n : ℕ, ∀ z : ℂ, dist z y ≤ ρ → dist (f^[n] z) y ≤ (1 / 2) ^ n * dist z y := by
  intro n
  induction n with
  | zero =>
      intro z _
      simp
  | succ n ih =>
      intro z hz
      -- The n-th iterate stays inside the ball of radius ρ, so that hstep applies.
      have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have hmem : dist (f^[n] z) y ≤ ρ := by
        calc dist (f^[n] z) y ≤ (1 / 2) ^ n * dist z y := ih z hz
          _ ≤ dist z y := by
              simpa using mul_le_mul_of_nonneg_right hp (dist_nonneg : (0 : ℝ) ≤ dist z y)
          _ ≤ ρ := hz
      calc dist (f^[n.succ] z) y = dist (f (f^[n] z)) y := by rw [Function.iterate_succ_apply']
        _ ≤ (1 / 2) * dist (f^[n] z) y := hstep _ hmem
        _ ≤ (1 / 2) * ((1 / 2) ^ n * dist z y) := by
              exact mul_le_mul_of_nonneg_left (ih z hz) (by norm_num)
        _ = (1 / 2) ^ n.succ * dist z y := by
              rw [pow_succ]; ring

end Work.Normal
