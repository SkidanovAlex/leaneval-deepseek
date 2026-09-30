import Mathlib
import Submission.Work.Space.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Space.Data

/-! **Constraint (ii) of blueprint §1**: `|σ_v| ≥ 2π e^{R₀}` with `R₀ = 7/2`, in the exact
rational form `(2π e^(7/2))² ≤ ‖σ_v‖²`.

In cube units `‖σ_v‖² = 44101` for `v ≤ 4` and `44948` for `v = 5` (`Work.Space.slopeNormSq`).
The ingredients are Mathlib's rational bounds
`Real.pi_lt_d20 : Real.pi < 3.14159265358979323847` and
`Real.exp_one_lt_d9 : Real.exp 1 < 2.7182818286`, together with
`Real.exp (7/2) = Real.exp 3 * Real.exp (1/2) = (Real.exp 1)^3 * √(Real.exp 1)`
(`Real.exp_add`, `Real.exp_nat_mul`, `Real.exp_half`, `Real.sq_sqrt`); it is enough to show
`Real.exp (7/2) < 167/5` (indeed `Real.exp 1 < 2.7182818286` gives
`(Real.exp 1)^3 < 20.0856` and `√(Real.exp 1) < 1.6488` because `1.6488^2 > 2.7182818286`,
so the product is `< 33.118 < 167/5 = 33.4`), and then `2π·(167/5) < 7348/35` is below
`√44101 = 210.0024`.  `fin_cases v` reduces the five cases to arithmetic
(`Work.Space.slopeNormSq` is a literal vector and `decide`/`norm_num` evaluates it). -/

/-- The numerical bound on the exponential that drives constraint (ii):
`e^{R₀} = e^{7/2} < 167/5`, obtained from `Real.exp 1 < 2.7182818286` by writing
`e^{7/2} = (e^1)^3 · √(e^1)` and bounding `(e^1)^3 < 20.0856`, `√(e^1) < 1.6488`. -/
theorem exp_seven_halves_lt : Real.exp ((7:ℝ)/2) < 167/5 := by
  have h1 : Real.exp ((7:ℝ)/2) = Real.exp 3 * Real.exp (1/2) := by
    rw [← Real.exp_add]; norm_num
  rw [h1]
  have h3 : Real.exp (3:ℝ) = (Real.exp 1)^3 := by
    rw [show (3:ℝ) = (3:ℕ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h3]
  have h2 : Real.exp ((1:ℝ)/2) = Real.sqrt (Real.exp 1) := Real.exp_half 1
  rw [h2]
  have hE : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hp3 : (Real.exp 1)^3 < (2.7182818286:ℝ)^3 :=
    pow_lt_pow_left₀ hE (Real.exp_pos 1).le (by norm_num)
  have hs : Real.sqrt (Real.exp 1) < (1.6488:ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 1.6488)]
    linarith [hE]
  calc (Real.exp 1)^3 * Real.sqrt (Real.exp 1)
      < (2.7182818286:ℝ)^3 * 1.6488 :=
        mul_lt_mul'' hp3 hs (pow_nonneg (Real.exp_pos 1).le 3) (Real.sqrt_nonneg _)
    _ < 167/5 := by norm_num

theorem slope_norm_ge (v : Fin 5) :
    (2 * Real.pi * Real.exp (7/2)) ^ 2 ≤ (slopeNormSq v : ℝ) := by
  have hmain : (2 * Real.pi * Real.exp (7/2)) ^ 2 < (44101:ℝ) := by
    have hpexp : Real.pi * Real.exp ((7:ℝ)/2) < 3.14159265358979323847 * (167/5) :=
      mul_lt_mul'' Real.pi_lt_d20 exp_seven_halves_lt Real.pi_pos.le (Real.exp_pos _).le
    have hb : 2 * Real.pi * Real.exp (7/2) < 210 := by nlinarith [hpexp]
    have hsq := pow_lt_pow_left₀ hb (by positivity) (by norm_num : (2:ℕ) ≠ 0)
    norm_num at hsq
    linarith [hsq]
  fin_cases v <;> simp [Work.Space.slopeNormSq] <;> linarith

end Work.Space.Data
