/-
# The numerical comparisons for the collar window `sTop = 33/20`

The unslabbed collar chart uses the height window `(s₁, sTop)` with `sTop = 33/20`
(`Work.Cusp.sTop`).  Three comparisons make it work.

* `sJ_lt_sTop : s_J = √e < 33/20`, so that the window contains the *junction* `s = s_J` of the inner
  and outer charts — equivalently `e < (33/20)² = 1089/400 = 2.7225`, which is the very loose
  `e < 2.7182818286` (`Real.exp_one_lt_d9`).
* `sTop_mul_betaMax_lt_sJ_sq : sTop · β_max = 99/40 = 2.475 < e = s_J²`, hence
  `beta_mul_sTop_lt_sJ_sq : β(x) · s < s_J²` for every ceiling `β(x)` and every height `s < sTop`.
  This is what makes the layer parameter

  `t = 1 + (log s − log β(x)) / (2 (log β(x) − log s_J))`

  recovered by `cuspInvOuter` **positive** (indeed `≤ 1`, since `s ≥ β(x)` above the ceiling).
* `sTop_sq_mul_betaMax_lt_sJ_cu : sTop² · β_max = 3267/800 = 4.08375 < e^{3/2} = s_J³`, hence
  `sTop_sq_mul_beta_lt_sJ_cu : β(x) · s² < s_J³`.  As `t = 1 − (log s − log β(x)) / (2 J)` with
  `J = log s_J − log β(x) > 0`, the bound `t > 1/4` is *equivalent* to `s² · β(x) < s_J³`, so the
  recovered layer parameter is bounded strictly away from the core `0` (this is what makes the layer
  chart `layerPtI` an open embedding).  The comparison is `e^{3/2} = e·√e > 2.7182818283 · 8/5` with
  `√e > 8/5` from `e > 64/25`, both rational.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.beta_min_le
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.s1_lt_betaMin
import Submission.Work.Cusp.beta_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real

/-- `s_J² = exp 1`, because `s_J = exp (1/2)`. -/
theorem sJ_sq : sJ ^ 2 = Real.exp 1 := by
  rw [sJ, ← Real.exp_nat_mul]
  norm_num

/-- `s_J³ = exp 1 · s_J`, because `s_J = exp (1/2)`. -/
theorem sJ_cu : sJ ^ 3 = Real.exp 1 * sJ := by
  rw [show sJ ^ 3 = sJ ^ 2 * sJ by ring, sJ_sq]

/-- `√e = s_J > 8/5`, from `e > 64/25`. -/
theorem eight_fifths_lt_sJ : (8/5 : ℝ) < sJ := by
  have h : (8/5 : ℝ) ^ 2 < sJ ^ 2 := by rw [sJ_sq]; nlinarith [Real.exp_one_gt_d9]
  exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt (Real.exp_pos (1/2))) h

/-- `0 < sTop`. -/
theorem sTop_pos : (0 : ℝ) < sTop := by norm_num [sTop]

/-- `s₁ = 11/10 < sTop = 33/20`. -/
theorem s1_lt_sTop : s1 < sTop := by norm_num [s1, sTop]

/-- `0 < betaMax`. -/
theorem betaMax_pos : (0 : ℝ) < betaMax := by norm_num [betaMax]

/-- **The junction `s_J = √e` lies inside the collar window**: `s_J < sTop = 33/20`, i.e.
`e < (33/20)² = 2.7225`. -/
theorem sJ_lt_sTop : sJ < sTop := by
  have hlt : sJ ^ 2 < (sTop : ℝ) ^ 2 := by
    rw [sJ_sq, sTop]; nlinarith [Real.exp_one_lt_d9]
  exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt sTop_pos) hlt

/-- **`β_max = 3/2` is below the top of the collar window**: `β_max < s_J < sTop`. -/
theorem betaMax_lt_sTop : betaMax < sTop := lt_trans betaMax_lt_sJ sJ_lt_sTop

/-- **Every ceiling is strictly below the top of the collar window**: `β x < sTop`. -/
theorem beta_lt_sTop (x : E3) : beta x < sTop :=
  lt_of_le_of_lt (beta_le_max x) betaMax_lt_sTop

/-- **Every ceiling is strictly above the horotorus level**: `s₁ < β x`. -/
theorem s1_lt_beta (x : E3) : s1 < beta x := lt_of_lt_of_le s1_lt_betaMin (beta_min_le x)

/-- **`β_max · sTop < s_J²`**: `(3/2)(33/20) = 99/40 = 2.475 < 2.7182818283 < e`. -/
theorem betaMax_mul_sTop_lt_sJ_sq : betaMax * sTop < sJ ^ 2 := by
  rw [sJ_sq, sTop, betaMax]
  nlinarith [Real.exp_one_gt_d9]

/-- **`β_max · sTop² < s_J³`**: `(3/2)(33/20)² = 3267/800 = 4.08375 < e·√e` with `e > 2.7182818283`
and `√e > 8/5`. -/
theorem betaMax_mul_sTop_sq_lt_sJ_cu : betaMax * sTop ^ 2 < sJ ^ 3 := by
  rw [sJ_cu]
  have hexp : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hsJ : (8/5 : ℝ) < sJ := eight_fifths_lt_sJ
  rw [sTop, betaMax]
  nlinarith [hexp, hsJ, Real.exp_pos 1]

/-- **`β(x) · s < s_J²` for every height `s` below the top of the window.** -/
theorem beta_mul_sTop_lt_sJ_sq (x : E3) : beta x * sTop < sJ ^ 2 := by
  have h1 : beta x * sTop ≤ betaMax * sTop :=
    mul_le_mul_of_nonneg_right (beta_le_max x) (le_of_lt sTop_pos)
  linarith [betaMax_mul_sTop_lt_sJ_sq]

/-- **`β(x) · s² < s_J³` for every height `s` below the top of the window.** -/
theorem beta_mul_sTop_sq_lt_sJ_cu (x : E3) : beta x * sTop ^ 2 < sJ ^ 3 := by
  have h1 : beta x * sTop ^ 2 ≤ betaMax * sTop ^ 2 :=
    mul_le_mul_of_nonneg_right (beta_le_max x) (by positivity)
  linarith [betaMax_mul_sTop_sq_lt_sJ_cu]

end Work.Cusp
