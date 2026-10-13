import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.Consts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.RadGreenSupp

theorem cmp3 {α a b M z : ℝ} {m : ℕ} (hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M)
    (hm : 1 ≤ m) (hz : 0 < z) (hbz : b ≤ z) :
    Work.FTS.EllExist.rgK α m
        * (z ^ (-(Work.FTS.EllExist.rgQ α m))
            * (M * b ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m))
      ≤ Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
  -- The whole content is `rgK/q · M · (b/z)^q ≤ C·M·z^{2/α}/(1+z)^{7/α}` for `z ≥ b`: the
  -- factor `(b/z)^q` is dominated by the third summand of `C`, namely
  -- `(1/63)(1+b)^{7/α} b^{-2/α} · z^{2/α}/(1+z)^{7/α} ≥ (1/63)(b/z)^{7/α} ≥ (1/63)(b/z)^q`,
  -- using `z ≥ b` (so `b/z ≤ (1+b)/(1+z)`) and `q ≥ 7/α ≥ 0`.
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hq7 : 7 / α ≤ Work.FTS.EllExist.rgQ α m :=
    Work.FTS.PhiStar.Honesty.RadGreenSupp.seven_div_alpha_le_rgQ hα hm
  have hbz1 : 0 < 1 + z := by linarith
  have hb1 : 0 < 1 + b := by linarith
  have hbz0 : 0 ≤ b / z := div_nonneg hb.le hz.le
  have hbzpos : 0 < b / z := div_pos hb hz
  have hbzle1 : b / z ≤ 1 := (div_le_one hz).mpr hbz
  have hstep1 : Work.FTS.EllExist.rgK α m
        * (z ^ (-(Work.FTS.EllExist.rgQ α m))
            * (M * b ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m))
      = (Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m) * M
          * (b / z) ^ (Work.FTS.EllExist.rgQ α m) := by
    rw [Real.div_rpow hb.le hz.le, Real.rpow_neg hz.le]
    ring_nf
  have h2 : (b / z) ^ (Work.FTS.EllExist.rgQ α m) ≤ (b / z) ^ (7 / α) :=
    Real.rpow_le_rpow_of_exponent_ge hbzpos hbzle1 hq7
  have hKq : Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m ≤ 1 / 63 :=
    Work.FTS.PhiStar.Honesty.RadGreenSupp.rgK_div_rgQ_le hα hm
  have h3 : (Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m)
        * (M * (b / z) ^ (Work.FTS.EllExist.rgQ α m))
      ≤ (1 / 63) * (M * (b / z) ^ (7 / α)) :=
    mul_le_mul hKq (mul_le_mul_of_nonneg_left h2 hM)
      (mul_nonneg hM (Real.rpow_nonneg hbz0 _)) (by norm_num)
  have h4a : b / z ≤ (1 + b) / (1 + z) := by
    rw [div_le_div_iff₀ hz hbz1]; linarith
  have h4 : (b / z) ^ (7 / α) ≤ ((1 + b) / (1 + z)) ^ (7 / α) :=
    Real.rpow_le_rpow hbz0 h4a (by positivity)
  have h4' : (1 / 63) * (M * (b / z) ^ (7 / α))
      ≤ (1 / 63) * (M * ((1 + b) / (1 + z)) ^ (7 / α)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hM) (by norm_num)
  have h5a : (1 : ℝ) ≤ z / b := (one_le_div hb).mpr hbz
  have h5b : (1 : ℝ) ≤ (z / b) ^ (2 / α) := Real.one_le_rpow h5a (by positivity)
  have hXnn : 0 ≤ ((1 + b) / (1 + z)) ^ (7 / α) :=
    Real.rpow_nonneg (by positivity) _
  have h5 : (1 / 63) * (M * ((1 + b) / (1 + z)) ^ (7 / α))
      ≤ (1 / 63) * (M * ((z / b) ^ (2 / α) * ((1 + b) / (1 + z)) ^ (7 / α))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hXnn h5b) hM) (by norm_num)
  have h6eq : (1 / 63) * (M * ((z / b) ^ (2 / α) * ((1 + b) / (1 + z)) ^ (7 / α)))
      = (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) * M
          * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
    rw [Real.div_rpow hz.le hb.le, Real.div_rpow hb1.le hbz1.le, Real.rpow_neg hb.le]
    ring
  have h6 : (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) * M
        * (z ^ (2 / α) / (1 + z) ^ (7 / α))
      ≤ Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b * M
          * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
    have hnn : 0 ≤ M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) :=
      mul_nonneg hM (div_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hbz1.le _))
    have hc := Work.FTS.PhiStar.Honesty.RadGreenSupp.C_term3_le
      (α := α) (a := a) (b := b) hα ha hab
    calc (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) * M
          * (z ^ (2 / α) / (1 + z) ^ (7 / α))
        = ((1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)))
            * (M * (z ^ (2 / α) / (1 + z) ^ (7 / α))) := by ring
      _ ≤ Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b
            * (M * (z ^ (2 / α) / (1 + z) ^ (7 / α))) :=
          mul_le_mul_of_nonneg_right hc hnn
      _ = Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b * M
            * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by ring
  calc Work.FTS.EllExist.rgK α m
        * (z ^ (-(Work.FTS.EllExist.rgQ α m))
            * (M * b ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m))
      = (Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m) * M
          * (b / z) ^ (Work.FTS.EllExist.rgQ α m) := hstep1
    _ = (Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgQ α m)
          * (M * (b / z) ^ (Work.FTS.EllExist.rgQ α m)) := by ring
    _ ≤ (1 / 63) * (M * (b / z) ^ (7 / α)) := h3
    _ ≤ (1 / 63) * (M * ((1 + b) / (1 + z)) ^ (7 / α)) := h4'
    _ ≤ (1 / 63) * (M * ((z / b) ^ (2 / α) * ((1 + b) / (1 + z)) ^ (7 / α))) := h5
    _ = (1 / 63) * (1 + b) ^ (7 / α) * b ^ (-(2 / α)) * M
          * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := h6eq
    _ ≤ Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b * M
          * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := h6

end Work.FTS.PhiStar.Honesty.RadGreenSupp
