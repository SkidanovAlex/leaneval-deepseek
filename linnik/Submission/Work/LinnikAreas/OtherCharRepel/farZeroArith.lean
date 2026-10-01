import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikAreas.OtherCharRepel.cosPolyDecent

namespace Work.LinnikAreas.OtherCharRepel

open DirichletCharacter Complex
open scoped Real

/-- The square-root data of the far-zero assembly: `√(5/4) = √5/2`, `√2 - √(5/4) > 0`, and
`(√2 - √(5/4))² = 13/4 - √10`. -/
theorem sqrtData :
    Real.sqrt (5 / 4) = Real.sqrt 5 / 2 ∧
    0 < Real.sqrt 2 - Real.sqrt (5 / 4) ∧
    (Real.sqrt 2 - Real.sqrt (5 / 4)) ^ 2 = 13 / 4 - Real.sqrt 10 := by
  have h5 : Real.sqrt (5 / 4) = Real.sqrt 5 / 2 := by
    have h : (0 : ℝ) ≤ Real.sqrt 5 / 2 := by positivity
    have h2 : (Real.sqrt 5 / 2) ^ 2 = 5 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]; norm_num
    rw [← h2]
    exact Real.sqrt_sq h
  have hpos : 0 < Real.sqrt 2 - Real.sqrt (5 / 4) := by
    rw [h5]
    have hlt : Real.sqrt 5 / 2 < Real.sqrt 2 := by
      rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2)]
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5),
        Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 5, Real.sqrt_nonneg 2]
    linarith
  have h10 : Real.sqrt 2 * Real.sqrt 5 = Real.sqrt 10 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  refine ⟨h5, hpos, ?_⟩
  rw [h5]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h5' : (Real.sqrt 5 / 2) ^ 2 = 5 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]; norm_num
  have key : (Real.sqrt 2 - Real.sqrt 5 / 2) ^ 2 = 2 - Real.sqrt 2 * Real.sqrt 5 + 5 / 4 := by
    rw [sub_sq, h2, h5']; ring
  rw [key, h10]
  ring

/-- **The `δ`-optimisation identity.**  For `ε > 0`, `s > 0`, `v > 0` with `(s+v)² = 2` and
`s² = 5/4`, the point `δ = s·ε/v` is the maximiser of `δ' ↦ 2/(δ'+ε) - (5/4)/δ'` and its value
there is `v²/ε`. -/
theorem keyArith {ε s v : ℝ} (hε : 0 < ε) (hv : 0 < v) (hs : 0 < s)
    (hsv : (s + v) ^ 2 = 2) (hs2 : s ^ 2 = 5 / 4) :
    2 / (s * ε / v + ε) - (5 / 4) / (s * ε / v) = v ^ 2 / ε := by
  have hvne : v ≠ 0 := ne_of_gt hv
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hsne : s ≠ 0 := ne_of_gt hs
  rw [← hs2]
  field_simp
  nlinarith [hsv]

/-- **The numerical closing inequality**: with the `1/16` safety margin, `(13/4 - √10) ≥ 9/128`,
which is the amount needed for `ε·log q ≥ (13/4 - √10)/((13/8)(17/16)) ≥ 1/25`. -/
theorem numBound : (1 / 25 : ℝ) ≤ (13 / 4 - Real.sqrt 10) * 128 / 221 := by
  have h10 : Real.sqrt 10 ≤ 407 / 128 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hmono : (13 / 4 - Real.sqrt 10) * 128 / 221 ≥ (13 / 4 - 407 / 128) * 128 / 221 := by
    have hpos : (0:ℝ) < 128 / 221 := by norm_num
    nlinarith [h10]
  have h2 : (13 / 4 - 407 / 128) * 128 / 221 = 9 / 221 := by norm_num
  have h3 : (1:ℝ) / 25 ≤ 9 / 221 := by norm_num
  linarith [hmono, h2, h3]

end Work.LinnikAreas.OtherCharRepel
