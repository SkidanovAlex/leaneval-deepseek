import Mathlib
import Submission.Work.CNum.Basic

/-! # `Work.CNum.AlpBound`

The cusp angle `alpR = arccos gamR`, for `c = 23/10`, `A = (1+c^2)^2`,
`gamR = 8c^2/A - 1 = 27559/395641`, satisfies `1.4973 < alpR < 1.5031`.

Writing `alpR = π/2 - arcsin gamR`, both inequalities reduce to rational bounds
on `arcsin` at the rational point `gamR = 27559/395641 ≈ 0.0696566`:

* `arcsin gamR ≤ 7/100`, because `gamR ≤ sin (7/100)` and `gamR ≤ sin (7/100)`
  follows from `sin x ≥ x - x^3/6 ≥ 7/100 - (7/100)^3/6 > gamR`;
* `arcsin gamR > 677/10000`, because `sin (677/10000) < 677/10000 < gamR` and
  `arcsin` is strictly increasing.

The two arcs are then separated with the rational bounds `3.1415 < π < 3.1416`. -/

namespace Work.CNum

lemma gamR_eq_rat : gamR = 27559 / 395641 := by norm_num [gamR, cR, AR]

theorem AlpBound : (1.4973 : ℝ) < Work.CNum.alpR ∧ Work.CNum.alpR < (1.5031 : ℝ) := by
  have hg : gamR = 27559 / 395641 := gamR_eq_rat
  have hg1 : gamR < 1 := by rw [hg]; norm_num
  -- upper bound for `arcsin gamR`
  have hsin_ub : gamR ≤ Real.sin (7 / 100) := by
    have h := Real.sin_ge_sub_cube (x := (7 / 100 : ℝ)) (by norm_num)
    have h2 : gamR ≤ (7 / 100 : ℝ) - (7 / 100) ^ 3 / 6 := by rw [hg]; norm_num
    linarith
  have hmem : (7 / 100 : ℝ) ∈ Set.Ico (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_gt_d4]
  have ha_up : Real.arcsin gamR ≤ 7 / 100 :=
    (Real.arcsin_le_iff_le_sin' (x := gamR) hmem).mpr hsin_ub
  -- lower bound for `arcsin gamR`
  have hsin_lb : Real.sin (677 / 10000) < gamR := by
    have h := Real.sin_lt (x := (677 / 10000 : ℝ)) (by norm_num)
    have h2 : (677 / 10000 : ℝ) < gamR := by rw [hg]; norm_num
    linarith
  have hmem2 : -(Real.pi / 2) ≤ (677 / 10000 : ℝ) := by linarith [Real.pi_pos]
  have hmem3 : (677 / 10000 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_d4]
  have hinv : Real.arcsin (Real.sin (677 / 10000)) = 677 / 10000 :=
    Real.arcsin_sin hmem2 hmem3
  have hmono : Real.arcsin (Real.sin (677 / 10000)) < Real.arcsin gamR :=
    Real.arcsin_lt_arcsin (Real.neg_one_le_sin (677 / 10000)) hsin_lb (le_of_lt hg1)
  have ha_lo : (677 / 10000 : ℝ) < Real.arcsin gamR := by rw [← hinv]; exact hmono
  rw [alpR, Real.arccos_eq_pi_div_two_sub_arcsin]
  constructor
  · linarith [ha_up, Real.pi_gt_d4]
  · linarith [ha_lo, Real.pi_lt_d4]

end Work.CNum
