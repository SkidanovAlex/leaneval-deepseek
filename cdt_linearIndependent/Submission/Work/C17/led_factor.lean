import Mathlib
import Submission.Work.C17.local_exp_data

namespace Work.C17

open Polynomial

/-! # Factorisation of the quartic `Q₄` over `ℂ`

`Q4x = 1 − 4abX + (4a²+4b²−2)X² − 4abX³ + X⁴` factors as
`(X² − ledC·X + 1)·(X² − ledD·X + 1)` over `ℂ`, where
`ledC = 2ab + 2√((a²−1)(b²−1))` and `ledD = 2ab − 2√((a²−1)(b²−1))`.

Indeed `ledC + ledD = 4ab` and `ledC·ledD + 2 = 4a²+4b²−2`, and the two quadratics
expand to the quartic.  The only analytic input is `(a²−1)(b²−1) ≥ 0` (so that
`√·² = ·`), which follows from `a, b ≥ 3`. -/

theorem led_factor (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    (Work.C17.Q4x a b).map (algebraMap ℚ ℂ)
      = (Polynomial.X ^ 2 - Polynomial.C (((Work.C17.ledC a b : ℝ)) : ℂ) * Polynomial.X + 1)
          * (Polynomial.X ^ 2 - Polynomial.C (((Work.C17.ledD a b : ℝ)) : ℂ) * Polynomial.X + 1) := by
  -- the square root is that of a nonnegative number
  have hD : 0 ≤ (((a:ℝ)^2 - 1) * ((b:ℝ)^2 - 1)) := by
    have ha' : (3:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
    have hb' : (3:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    have h1 : (0:ℝ) < (a:ℝ)^2 - 1 := by nlinarith [sq_nonneg ((a:ℝ) - 3)]
    have h2 : (0:ℝ) < (b:ℝ)^2 - 1 := by nlinarith [sq_nonneg ((b:ℝ) - 3)]
    exact mul_nonneg h1.le h2.le
  have hs : Real.sqrt (((a:ℝ)^2 - 1) * ((b:ℝ)^2 - 1))^2 = ((a:ℝ)^2 - 1) * ((b:ℝ)^2 - 1) :=
    Real.sq_sqrt hD
  -- Vieta: sum and product of the two values `z + 1/z`
  have hsum : 4 * (a:ℝ) * (b:ℝ) = ledC a b + ledD a b := by
    unfold ledC ledD; ring
  have hprod : 4*(a:ℝ)^2 + 4*(b:ℝ)^2 - 2 = ledC a b * ledD a b + 2 := by
    unfold ledC ledD
    nlinarith [hs]
  -- the factorisation over `ℝ`
  have hR : (Work.C17.Q4x a b).map (algebraMap ℚ ℝ)
      = (X^2 - C (ledC a b) * X + 1) * (X^2 - C (ledD a b) * X + 1) := by
    apply Polynomial.funext
    intro z
    simp only [Polynomial.eval_map, Q4x, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one]
    rw [show (algebraMap ℚ ℝ) (4 * a * b) = 4 * (a:ℝ) * (b:ℝ) from by norm_num,
        show (algebraMap ℚ ℝ) (4 * a ^ 2 + 4 * b ^ 2 - 2)
          = 4 * (a:ℝ)^2 + 4 * (b:ℝ)^2 - 2 from by norm_num]
    rw [hsum, hprod]
    ring
  -- transport along `ℚ → ℝ → ℂ`
  have hC := congrArg (Polynomial.map (algebraMap ℝ ℂ)) hR
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℚ ℝ ℂ] at hC
  simpa [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_one, Polynomial.map_C] using hC

end Work.C17
