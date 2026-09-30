/-
# The height of the collar stays strictly between the horotorus level `s₁` and the junction `s_J`

`collarHeight t b = exp ((2t-1) log b + (2-2t) log s_J)` is the UHS height of the outer chart
`Θ_v` at layer parameter `t = ‖p‖∞` and ceiling `b = β(x)` (`Basic.collarHeight`).  Since the
two coefficients `2t-1` and `2-2t` are nonnegative on `[1/2, 1]` and sum to `1`, the logarithm
of the collar height is a **convex combination** of `log b` and `log s_J`:

  `log (collarHeight t b) = (2t-1) log b + (2-2t) log s_J`,  `(2t-1) + (2-2t) = 1`, `2t-1, 2-2t ≥ 0`.

Hence, as soon as `b` lies in the range `[β_min, β_max] = [√(3/2), 3/2]` of the ceiling `β`, the
height is trapped between the two endpoints `b` and `s_J`:

* `collarHeight t b ≤ s_J` because `b ≤ β_max = 3/2 < s_J = e^{1/2}` (so `log b ≤ log s_J`), and
* `collarHeight t b > s₁` because `b ≥ β_min = √(3/2) > 11/10 = s₁` and `s_J > s₁`, so that

  `log (collarHeight t b) = log s₁ + (2t-1)(log b - log s₁) + (2-2t)(log s_J - log s₁)`

  with both differences strictly positive and the weights nonnegative summing to `1`; the
  weighted average of two positive numbers is at least their minimum, which is positive.

This is the standing estimate that keeps the collar `½ ≤ ‖p‖∞ ≤ 1` inside the slab
`s₁ < s ≤ s_J` of the upper half space, i.e. above every other facet of `Q̄` (level `s₁`) and at
or below the truncation torus `τ_v` (which is capped by the junction `s_J`).

The three numerical inputs are proved here from scratch (as `private` lemmas, so that the file is
self-contained):

* `0 < β_min = √(3/2)`,
* `s₁ = 11/10 < √(3/2) = β_min` (squaring both sides: `121/100 < 150/100`),
* `β_max = 3/2 < e^{1/2} = s_J` (via `log (3/2) < 3/2 - 1 = 1/2` and `x < e^y ↔ log x < y`).
-/
import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

/-- `β_min = √(3/2)` is positive. -/
private lemma betaMin_pos_aux : 0 < betaMin := by
  rw [betaMin]
  exact Real.sqrt_pos_of_pos (by norm_num)

/-- `s₁ = 11/10 < √(3/2) = β_min`; both sides are nonnegative, so it suffices to square:
`(11/10)² = 121/100 < 150/100 = 3/2`. -/
private lemma s1_lt_betaMin_aux : s1 < betaMin := by
  rw [s1, betaMin]
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- `β_max = 3/2 < e^{1/2} = s_J`.  Taking logarithms (`x < e^y ↔ log x < y` for `x > 0`), this
is `log (3/2) < 1/2`, which follows from `log x < x - 1` at `x = 3/2`. -/
private lemma betaMax_lt_sJ_aux : betaMax < sJ := by
  rw [betaMax, sJ]
  rw [← (Real.log_lt_iff_lt_exp (show (0 : ℝ) < 3/2 by norm_num))]
  have h := Real.log_lt_sub_one_of_pos (x := (3/2 : ℝ)) (by norm_num) (by norm_num)
  linarith

/-- `0 < s₁ = 11/10`. -/
private lemma s1_pos_aux : 0 < s1 := by rw [s1]; norm_num

/-- `0 < s_J = e^{1/2}`. -/
private lemma sJ_pos_aux : 0 < sJ := by rw [sJ]; exact Real.exp_pos _

/-- **The collar height lies strictly between the horotorus level `s₁` and the junction `s_J`.**
For `t ∈ [1/2, 1]` and any ceiling value `b` in the range of `β`, the UHS height
`collarHeight t b = β^{2t-1} s_J^{2-2t}` of the collar is `> s₁` and `≤ s_J` (see the file
header for the one-line estimate). -/
theorem collarHeight_mem (t b : ℝ) (ht : 1/2 ≤ t) (ht1 : t ≤ 1)
    (hb : betaMin ≤ b) (hb2 : b ≤ betaMax) : s1 < collarHeight t b ∧ collarHeight t b ≤ sJ := by
  have hbpos : 0 < b := lt_of_lt_of_le betaMin_pos_aux hb
  -- `b < s_J`, since `b ≤ β_max < s_J`
  have hb_lt_sJ : b < sJ := lt_of_le_of_lt hb2 betaMax_lt_sJ_aux
  have hlogb : Real.log b ≤ Real.log sJ := Real.log_le_log hbpos (le_of_lt hb_lt_sJ)
  have hs1_sJ : s1 < sJ := lt_trans (lt_of_lt_of_le s1_lt_betaMin_aux hb) hb_lt_sJ
  -- the two weights are nonnegative and sum to `1`
  have hA : 0 ≤ 2 * t - 1 := by linarith
  have hB : 0 ≤ 2 - 2 * t := by linarith
  have hAB : (2 * t - 1) + (2 - 2 * t) = 1 := by ring
  -- upper bound: replace `log b` by the larger `log s_J`
  have hupper : (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ ≤ Real.log sJ := by
    have h1 : (2 * t - 1) * Real.log b ≤ (2 * t - 1) * Real.log sJ :=
      mul_le_mul_of_nonneg_left hlogb hA
    have h2 : (2 * t - 1) * Real.log sJ + (2 - 2 * t) * Real.log sJ = Real.log sJ := by
      rw [← add_mul, hAB, one_mul]
    linarith
  -- lower bound: both `log b` and `log s_J` exceed `log s₁` strictly
  have hlower : Real.log s1 < (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ := by
    have hp : 0 < Real.log b - Real.log s1 :=
      sub_pos.mpr (Real.log_lt_log s1_pos_aux (lt_of_lt_of_le s1_lt_betaMin_aux hb))
    have hq : 0 < Real.log sJ - Real.log s1 :=
      sub_pos.mpr (Real.log_lt_log s1_pos_aux hs1_sJ)
    -- the weighted average of the two positive differences is at least their minimum
    set m := min (Real.log b - Real.log s1) (Real.log sJ - Real.log s1) with hm
    have hmpos : 0 < m := lt_min hp hq
    have hm1 : m ≤ Real.log b - Real.log s1 := min_le_left _ _
    have hm2 : m ≤ Real.log sJ - Real.log s1 := min_le_right _ _
    have hsum : m ≤ (2 * t - 1) * (Real.log b - Real.log s1)
        + (2 - 2 * t) * (Real.log sJ - Real.log s1) := by
      calc m = (2 * t - 1) * m + (2 - 2 * t) * m := by rw [← add_mul, hAB, one_mul]
        _ ≤ (2 * t - 1) * (Real.log b - Real.log s1)
              + (2 - 2 * t) * (Real.log sJ - Real.log s1) :=
            add_le_add (mul_le_mul_of_nonneg_left hm1 hA) (mul_le_mul_of_nonneg_left hm2 hB)
    have hsumpos : 0 < (2 * t - 1) * (Real.log b - Real.log s1)
        + (2 - 2 * t) * (Real.log sJ - Real.log s1) := lt_of_lt_of_le hmpos hsum
    have hexpand : (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ
        = Real.log s1 + ((2 * t - 1) * (Real.log b - Real.log s1)
            + (2 - 2 * t) * (Real.log sJ - Real.log s1)) := by ring
    rw [hexpand]
    linarith
  rw [collarHeight]
  constructor
  · calc s1 = Real.exp (Real.log s1) := (Real.exp_log s1_pos_aux).symm
      _ < Real.exp ((2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ) :=
          Real.exp_lt_exp.mpr hlower
  · calc Real.exp ((2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log sJ)
        ≤ Real.exp (Real.log sJ) := Real.exp_le_exp.mpr hupper
      _ = sJ := Real.exp_log sJ_pos_aux

end Work.Cusp
