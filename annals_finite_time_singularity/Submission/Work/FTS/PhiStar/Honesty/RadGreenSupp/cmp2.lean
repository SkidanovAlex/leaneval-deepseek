/-
# `RadGreenSupp.cmp2` — the middle regime of the weighted support bound

For `0 < a ≤ z ≤ b` the two indicial branches of the radial Green function combine to the
`z`-independent quantity `K·M·(1/q + 1/p) ≤ M/14` (`rgK_mul_inv_add_le`), while the weight on the
right, `z ^ (2/α) / (1+z) ^ (7/α)`, is at least `a ^ (2/α) / (1+b) ^ (7/α)`; the first `C`-summand
counted with `a` (from the lower end of the interval) and `b` (from the upper end) is exactly the
reciprocal of that, giving `C · M · weight ≥ M/14` (`Consts.C_term2_le`).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.Consts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.RadGreenSupp

set_option autoImplicit false

open Work.FTS.EllExist

/-- The "middle regime" weight comparison: for `0 < a ≤ z ≤ b`,
`a ^ (2/α) / (1+b) ^ (7/α) ≤ z ^ (2/α) / (1+z) ^ (7/α)`. -/
theorem middle_weight_le {α a b z : ℝ} (hα : 0 < α) (ha : 0 < a) (haz : a ≤ z) (hzb : z ≤ b) :
    a ^ (2 / α) / (1 + b) ^ (7 / α) ≤ z ^ (2 / α) / (1 + z) ^ (7 / α) := by
  have hz : 0 < z := lt_of_lt_of_le ha haz
  have hα2 : (0 : ℝ) < 2 / α := by positivity
  have hα7 : (0 : ℝ) < 7 / α := by positivity
  have hnum : a ^ (2 / α) ≤ z ^ (2 / α) := Real.rpow_le_rpow ha.le haz hα2.le
  have hden : (1 + z) ^ (7 / α) ≤ (1 + b) ^ (7 / α) :=
    Real.rpow_le_rpow (by linarith) (by linarith) hα7.le
  have hzden : 0 < (1 + z) ^ (7 / α) := Real.rpow_pos_of_pos (by linarith) _
  have hbden : 0 < (1 + b) ^ (7 / α) := Real.rpow_pos_of_pos (by linarith) _
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul hnum
    (by simpa [one_div] using one_div_le_one_div_of_le hzden hden)
    (inv_nonneg.mpr hbden.le) (Real.rpow_pos_of_pos hz _).le

/-- The `C`-summand `(1/14)·a ^ (-2/α)·(1+b) ^ (7/α)` times the middle-regime weight comparison
is exactly `1/14`. -/
theorem C_term2_mul_middle {α a b : ℝ} (ha : 0 < a) (hb : 0 < 1 + b) :
    ((1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α)) * (a ^ (2 / α) / (1 + b) ^ (7 / α))
      = 1 / 14 := by
  have hbden : (1 + b) ^ (7 / α) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hb _)
  rw [show ((1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α)) * (a ^ (2 / α) / (1 + b) ^ (7 / α))
      = (1 / 14) * (a ^ (-(2 / α)) * a ^ (2 / α)) * ((1 + b) ^ (7 / α) / (1 + b) ^ (7 / α))
      from by ring,
    ← Real.rpow_add ha, show -(2 / α) + 2 / α = 0 from by ring, Real.rpow_zero,
    div_self hbden]
  ring

theorem cmp2 {α a b M z : ℝ} {m : ℕ} (hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M)
    (hm : 1 ≤ m) (hz : 0 < z) (haz : a ≤ z) (hzb : z ≤ b) :
    Work.FTS.EllExist.rgK α m
        * (z ^ (-(Work.FTS.EllExist.rgQ α m))
              * (M * z ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m)
            + z ^ Work.FTS.EllExist.rgP α m
              * (M * z ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m))
      ≤ Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  -- the two branches collapse to `M/q` and `M/p`
  have h1 : z ^ (-(rgQ α m)) * (M * z ^ (rgQ α m) / rgQ α m) = M / rgQ α m := by
    rw [show z ^ (-(rgQ α m)) * (M * z ^ (rgQ α m) / rgQ α m)
        = M * (z ^ (-(rgQ α m)) * z ^ (rgQ α m)) / rgQ α m from by ring,
      ← Real.rpow_add hz, show -(rgQ α m) + rgQ α m = 0 from by ring, Real.rpow_zero]
    ring
  have h2 : z ^ (rgP α m) * (M * z ^ (-(rgP α m)) / rgP α m) = M / rgP α m := by
    rw [show z ^ (rgP α m) * (M * z ^ (-(rgP α m)) / rgP α m)
        = M * (z ^ (rgP α m) * z ^ (-(rgP α m))) / rgP α m from by ring,
      ← Real.rpow_add hz, show rgP α m + -(rgP α m) = 0 from by ring, Real.rpow_zero]
    ring
  have hL : rgK α m * (z ^ (-(rgQ α m)) * (M * z ^ (rgQ α m) / rgQ α m)
        + z ^ (rgP α m) * (M * z ^ (-(rgP α m)) / rgP α m))
      = M * (rgK α m * (1 / rgQ α m + 1 / rgP α m)) := by
    rw [h1, h2]
    rw [show M / rgQ α m + M / rgP α m = M * (1 / rgQ α m + 1 / rgP α m) from by ring]
    ring
  -- the arithmetic constant of the two indicial exponents
  have hK : rgK α m * (1 / rgQ α m + 1 / rgP α m) ≤ 1 / 14 := rgK_mul_inv_add_le hα hm
  -- the weight on the right is bounded below by its value at `a`, `b`
  have hratio : a ^ (2 / α) / (1 + b) ^ (7 / α) ≤ z ^ (2 / α) / (1 + z) ^ (7 / α) :=
    middle_weight_le hα ha haz hzb
  have hratio1nn : 0 ≤ a ^ (2 / α) / (1 + b) ^ (7 / α) :=
    div_nonneg (Real.rpow_pos_of_pos ha _).le
      (Real.rpow_pos_of_pos (by linarith) _).le
  have hratio2nn : 0 ≤ z ^ (2 / α) / (1 + z) ^ (7 / α) :=
    div_nonneg (Real.rpow_pos_of_pos hz _).le
      (Real.rpow_pos_of_pos (by linarith) _).le
  have hc2 : (1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α) ≤ C α a b := C_term2_le hα ha hab
  have hCnn : 0 ≤ C α a b := (C_pos hα ha hab).le
  have hprod : ((1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α))
        * (M * (a ^ (2 / α) / (1 + b) ^ (7 / α)))
      ≤ C α a b * (M * (z ^ (2 / α) / (1 + z) ^ (7 / α))) :=
    mul_le_mul hc2 (mul_le_mul_of_nonneg_left hratio hM) (mul_nonneg hM hratio1nn) hCnn
  have hleft : ((1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α))
        * (M * (a ^ (2 / α) / (1 + b) ^ (7 / α))) = M / 14 := by
    rw [show ((1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α))
          * (M * (a ^ (2 / α) / (1 + b) ^ (7 / α)))
        = M * (((1 / 14) * a ^ (-(2 / α)) * (1 + b) ^ (7 / α))
          * (a ^ (2 / α) / (1 + b) ^ (7 / α))) from by ring,
      C_term2_mul_middle ha (by linarith : (0:ℝ) < 1 + b)]
    ring
  have hstep2 : M / 14 ≤ C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
    rw [hleft] at hprod
    rwa [← mul_assoc] at hprod
  rw [hL]
  linarith [mul_le_mul_of_nonneg_left hK hM, hstep2]

end Work.FTS.PhiStar.Honesty.RadGreenSupp
