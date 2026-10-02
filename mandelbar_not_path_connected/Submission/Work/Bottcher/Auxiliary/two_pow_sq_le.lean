import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Aux

/-- Auxiliary estimate for the Böttcher coordinate bounds: if `B 0 ≥ 2` and
`B (n+1) ≥ B n ^ 4 / 2`, then `B n ≥ 2 ^ (2 * n)`.

The direct induction does not close at `n = 0` (the quartic step has only
just enough room from `n = 1` onwards), so we use two-step induction:
the case `n = 1` is checked directly, and the induction step uses the
hypothesis at `n + 1`, for which the exponent inequality
`2 * (n+2) + 1 ≤ (2 * (n+1)) * 4` always holds. -/
theorem two_pow_sq_le (B : ℕ → ℝ) (h0 : 2 ≤ B 0) (hstep : ∀ n, B n ^ 4 / 2 ≤ B (n + 1)) :
    ∀ n, (2 : ℝ) ^ (2 * n) ≤ B n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      norm_num
      linarith
  | one =>
      have h0' : (2 : ℝ) ^ 4 ≤ B 0 ^ 4 := pow_le_pow_left₀ (by norm_num) h0 4
      have hh : (2 : ℝ) ^ 4 / 2 ≤ B 0 ^ 4 / 2 := by linarith
      have h1 := hstep 0
      have : (2 : ℝ) ^ 4 / 2 ≤ B (0 + 1) := le_trans hh h1
      norm_num at this ⊢
      linarith
  | more n _ih1 ih2 =>
      have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * (n + 1)) := by positivity
      have h4 : ((2 : ℝ) ^ (2 * (n + 1))) ^ 4 ≤ (B (n + 1)) ^ 4 :=
        pow_le_pow_left₀ hpos ih2 4
      have hstep' : (B (n + 1)) ^ 4 / 2 ≤ B (n + 2) := by
        have h := hstep (n + 1)
        rwa [show (n + 1) + 1 = n + 2 by omega] at h
      have key : (2 : ℝ) ^ (2 * (n + 2)) * 2 ≤ ((2 : ℝ) ^ (2 * (n + 1))) ^ 4 := by
        have h : (2 : ℝ) ^ (2 * (n + 2) + 1) ≤ (2 : ℝ) ^ ((2 * (n + 1)) * 4) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        rw [pow_succ] at h
        have h' : (2 : ℝ) ^ ((2 * (n + 1)) * 4) = ((2 : ℝ) ^ (2 * (n + 1))) ^ 4 := by
          rw [pow_mul]
        rw [h'] at h
        exact h
      have hB : (B (n + 1)) ^ 4 ≤ B (n + 2) * 2 :=
        (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hstep'
      have hfin : (2 : ℝ) ^ (2 * (n + 2)) * 2 ≤ B (n + 2) * 2 :=
        le_trans key (le_trans h4 hB)
      exact le_of_mul_le_mul_right hfin (by norm_num)

end Work.Bottcher.Aux
