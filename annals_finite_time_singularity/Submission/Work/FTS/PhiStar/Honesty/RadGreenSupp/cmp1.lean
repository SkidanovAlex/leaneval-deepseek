import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.Consts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.RadGreenSupp

/-- **The head regime `z ≤ a` of the weighted support bound.**

With `K = rgK α m`, `p = rgP α m`, the head estimate of `radGreen_supp_weight_le` compares the
growing-branch contribution `K·z^p·(M·a^{-p}/p)` — which is what `|radGreen|` reduces to for
`z ≤ a` when `c` is supported in `[a,b]` with `|c| ≤ M` — with the two-sided bound
`C α a b · M · z^{2/α}/(1+z)^{7/α}`.

Since `z ≤ a` we have `z^p·a^{-p} = (z/a)^p`, and `K/p = 1/(2m(4m+5)) ≤ 1/18` (`rgK_div_rgP_le`),
so the left side is at most `(M/18)·(z/a)^p`.  Because `p = 2m/α ≥ 2/α` and `z/a ≤ 1` this is at
most `(M/18)·(z/a)^{2/α} = (M/18)·z^{2/α}a^{-2/α}`, while the first summand of `C` alone
(`C_term1_le`) already gives `2·(M/2)·z^{2/α}a^{-2/α} = M·z^{2/α}a^{-2/α} ≥ (M/18)·z^{2/α}a^{-2/α}`,
using `(1+z)^{7/α} ≤ (1+a)^{7/α}` (from `z ≤ a`). -/
theorem cmp1 {α a b M z : ℝ} {m : ℕ} (hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M)
    (hm : 1 ≤ m) (hz : 0 < z) (hza : z ≤ a) :
    Work.FTS.EllExist.rgK α m
        * (z ^ Work.FTS.EllExist.rgP α m
            * (M * a ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m))
      ≤ Work.FTS.PhiStar.Honesty.RadGreenSupp.C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
  have hza_pos : 0 < z / a := div_pos hz ha
  have hza1 : z / a ≤ 1 := (div_le_one ha).mpr hza
  have h2ap : 2 / α ≤ Work.FTS.EllExist.rgP α m := two_div_alpha_le_rgP hα hm
  have hKp : Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgP α m ≤ 1 / 18 :=
    rgK_div_rgP_le hα hm
  have hdiv : z ^ Work.FTS.EllExist.rgP α m * a ^ (-(Work.FTS.EllExist.rgP α m))
      = (z / a) ^ Work.FTS.EllExist.rgP α m := by
    rw [Real.div_rpow hz.le ha.le, Real.rpow_neg ha.le]
    ring
  have hL : Work.FTS.EllExist.rgK α m
        * (z ^ Work.FTS.EllExist.rgP α m
            * (M * a ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m))
      = M * (Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgP α m)
          * (z / a) ^ Work.FTS.EllExist.rgP α m := by
    rw [← hdiv]
    ring
  have hXleY : (z / a) ^ Work.FTS.EllExist.rgP α m ≤ (z / a) ^ (2 / α) :=
    Real.rpow_le_rpow_of_exponent_ge hza_pos hza1 h2ap
  have hQ : (z / a) ^ (2 / α) = z ^ (2 / α) * a ^ (-(2 / α)) := by
    rw [Real.div_rpow hz.le ha.le, Real.rpow_neg ha.le]
    ring
  have hden : 0 < (1 + z) ^ (7 / α) := Real.rpow_pos_of_pos (by linarith) _
  have hr1 : 1 ≤ (1 + a) ^ (7 / α) / (1 + z) ^ (7 / α) := by
    rw [one_le_div hden]
    exact Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
  have hCt1 : (1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α) ≤ C α a b :=
    C_term1_le hα ha hab
  have hD : 0 ≤ z ^ (2 / α) / (1 + z) ^ (7 / α) := by positivity
  have hCnonneg : 0 ≤ C α a b := le_of_lt (C_pos hα ha hab)
  have hfac2 : (1 / 2) * a ^ (-(2 / α)) * z ^ (2 / α)
      ≤ ((1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α)) * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
    have h0 : 0 ≤ (1 / 2) * a ^ (-(2 / α)) * z ^ (2 / α) := by
      have h1 : 0 ≤ a ^ (-(2 / α)) := Real.rpow_nonneg ha.le _
      have h2 : 0 ≤ z ^ (2 / α) := Real.rpow_nonneg hz.le _
      positivity
    calc (1 / 2) * a ^ (-(2 / α)) * z ^ (2 / α)
        = (1 / 2) * a ^ (-(2 / α)) * z ^ (2 / α) * 1 := by ring
      _ ≤ (1 / 2) * a ^ (-(2 / α)) * z ^ (2 / α) * ((1 + a) ^ (7 / α) / (1 + z) ^ (7 / α)) :=
            mul_le_mul_of_nonneg_left hr1 h0
      _ = ((1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α)) * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
            ring
  have hmid : M * (1 / 2) * (z / a) ^ (2 / α)
      ≤ C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
    have heq : M * (1 / 2) * (z / a) ^ (2 / α) = M * ((1 / 2) * a ^ (-(2 / α)) * z ^ (2 / α)) := by
      rw [hQ]; ring
    rw [heq]
    refine le_trans (mul_le_mul_of_nonneg_left hfac2 hM) ?_
    have hCM : ((1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α)) * M ≤ C α a b * M :=
      mul_le_mul hCt1 le_rfl hM hCnonneg
    have h := mul_le_mul_of_nonneg_right hCM hD
    have e1 : M * (((1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α))
          * (z ^ (2 / α) / (1 + z) ^ (7 / α)))
        = ((1 / 2) * a ^ (-(2 / α)) * (1 + a) ^ (7 / α)) * M
            * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by ring
    rw [e1]
    exact h
  calc Work.FTS.EllExist.rgK α m
        * (z ^ Work.FTS.EllExist.rgP α m
            * (M * a ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m))
      = M * (Work.FTS.EllExist.rgK α m / Work.FTS.EllExist.rgP α m)
          * (z / a) ^ Work.FTS.EllExist.rgP α m := hL
    _ ≤ M * (1 / 18) * (z / a) ^ Work.FTS.EllExist.rgP α m := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKp hM)
          (Real.rpow_nonneg hza_pos.le _)
    _ ≤ M * (1 / 2) * (z / a) ^ (2 / α) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (by norm_num) hM) hXleY
          (Real.rpow_nonneg hza_pos.le _) (by positivity)
    _ ≤ C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := hmid

end Work.FTS.PhiStar.Honesty.RadGreenSupp
