import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseK15.AlphaAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseK15.h_lipschitz` — the one-variable Bogoliubov angle is `4`-Lipschitz on `[-1/2,1/2]`

`h r = r/(1 + √(1-r²))` is the `tan(½·arcsin r)` parametrisation of the Bogoliubov
squeezing angle (`Work.BoseK15.AlphaAux`).  This file proves the quantitative
Lipschitz bound used downstream:

`|h r - h r'| ≤ 4 * |r - r'|` whenever `|r| ≤ 1/2` and `|r'| ≤ 1/2`.

The proof is elementary.  With `u = √(1-r²)`, `u' = √(1-r'²)` (both `≥ 1/2` on the
range considered, since `1-r² ≥ 3/4`), one has

`h r - h r' = ((r - r') + (r u' - r' u)) / ((1+u)(1+u'))`,

so `|h r - h r'| ≤ |r-r'| + |r u' - r' u|`.  Moreover
`|u' - u| = |r² - r'²|/(u+u') ≤ |r-r'|·|r+r'| ≤ |r-r'|`, whence
`|r u' - r' u| ≤ |r-r'|·u' + |r'|·|u'-u| ≤ (3/2)|r-r'|`.  Summing gives
`(5/2)|r-r'| ≤ 4|r-r'|`.
-/

noncomputable section

namespace Work.BoseK15

theorem h_lipschitz {r r' : ℝ} (hr : |r| ≤ 1 / 2) (hr' : |r'| ≤ 1 / 2) :
    |Work.BoseK15.h r - Work.BoseK15.h r'| ≤ 4 * |r - r'| := by
  set u : ℝ := Real.sqrt (1 - r ^ 2) with hu
  set u' : ℝ := Real.sqrt (1 - r' ^ 2) with hu'
  have hr_le : r ≤ 1 / 2 := (abs_le.mp hr).2
  have hr_ge : -(1 / 2) ≤ r := (abs_le.mp hr).1
  have hr'_le : r' ≤ 1 / 2 := (abs_le.mp hr').2
  have hr'_ge : -(1 / 2) ≤ r' := (abs_le.mp hr').1
  have h1 : 0 ≤ 1 - r ^ 2 := by nlinarith
  have h1' : 0 ≤ 1 - r' ^ 2 := by nlinarith
  have hu2 : u ^ 2 = 1 - r ^ 2 := by rw [hu]; exact Real.sq_sqrt h1
  have hu'2 : u' ^ 2 = 1 - r' ^ 2 := by rw [hu']; exact Real.sq_sqrt h1'
  have hu_half : 1 / 2 ≤ u := by
    rw [hu, Real.le_sqrt (by norm_num) h1]
    nlinarith
  have hu'_half : 1 / 2 ≤ u' := by
    rw [hu', Real.le_sqrt (by norm_num) h1']
    nlinarith
  have hu_nn : 0 ≤ u := le_trans (by norm_num) hu_half
  have hu'_nn : 0 ≤ u' := le_trans (by norm_num) hu'_half
  have hden_pos : 0 < (1 + u) * (1 + u') := by nlinarith
  have key : Work.BoseK15.h r - Work.BoseK15.h r' =
      ((r - r') + (r * u' - r' * u)) / ((1 + u) * (1 + u')) := by
    unfold Work.BoseK15.h
    rw [← hu, ← hu', div_sub_div r r' (by linarith : 1 + u ≠ 0) (by linarith : 1 + u' ≠ 0)]
    ring
  have habs : |Work.BoseK15.h r - Work.BoseK15.h r'| =
      |(r - r') + (r * u' - r' * u)| / ((1 + u) * (1 + u')) := by
    rw [key, abs_div, abs_of_pos hden_pos]
  have hstep1 : |Work.BoseK15.h r - Work.BoseK15.h r'| ≤ |r - r'| + |r * u' - r' * u| := by
    rw [habs]
    have hle : |(r - r') + (r * u' - r' * u)| ≤ |r - r'| + |r * u' - r' * u| := abs_add_le _ _
    refine le_trans (div_le_div_of_nonneg_right hle hden_pos.le) ?_
    exact div_le_self (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by nlinarith)
  have hdiff : |u' - u| ≤ |r - r'| := by
    have hsum : 0 < u + u' := by linarith
    have hE : u' - u = (r ^ 2 - r' ^ 2) / (u + u') := by
      rw [eq_div_iff (by linarith : u + u' ≠ 0)]
      nlinarith [hu2, hu'2]
    rw [hE, abs_div, abs_of_pos hsum]
    have hfact : r ^ 2 - r' ^ 2 = (r - r') * (r + r') := by ring
    have hrs : |r + r'| ≤ 1 := by
      have := abs_add_le r r'
      linarith
    have hnumle : |r ^ 2 - r' ^ 2| ≤ |r - r'| := by
      rw [hfact, abs_mul]
      calc |r - r'| * |r + r'| ≤ |r - r'| * 1 := mul_le_mul_of_nonneg_left hrs (abs_nonneg _)
        _ = |r - r'| := by ring
    calc |r ^ 2 - r' ^ 2| / (u + u') ≤ |r ^ 2 - r' ^ 2| :=
          div_le_self (abs_nonneg _) (by linarith)
      _ ≤ |r - r'| := hnumle
  have hu'_le_one : u' ≤ 1 := by
    have h2 : u' ^ 2 ≤ 1 := by nlinarith [hu'2]
    have h3 := (sq_le_one_iff_abs_le_one u').mp h2
    exact (abs_le.mp h3).2
  have hmid : |r * u' - r' * u| ≤ (3 / 2) * |r - r'| := by
    have hdecomp : r * u' - r' * u = (r - r') * u' + r' * (u' - u) := by ring
    rw [hdecomp]
    have h1 : |(r - r') * u' + r' * (u' - u)| ≤ |(r - r') * u'| + |r' * (u' - u)| := abs_add_le _ _
    rw [abs_mul, abs_mul, abs_of_nonneg hu'_nn] at h1
    have h2 : |r - r'| * u' ≤ |r - r'| := by
      have := mul_le_mul_of_nonneg_left hu'_le_one (abs_nonneg (r - r'))
      simpa using this
    have h3 : |r'| * |u' - u| ≤ (1 / 2) * |r - r'| :=
      mul_le_mul hr' hdiff (abs_nonneg _) (by norm_num)
    linarith
  calc |Work.BoseK15.h r - Work.BoseK15.h r'| ≤ |r - r'| + |r * u' - r' * u| := hstep1
    _ ≤ |r - r'| + (3 / 2) * |r - r'| := by linarith
    _ ≤ 4 * |r - r'| := by nlinarith [abs_nonneg (r - r')]

end Work.BoseK15
