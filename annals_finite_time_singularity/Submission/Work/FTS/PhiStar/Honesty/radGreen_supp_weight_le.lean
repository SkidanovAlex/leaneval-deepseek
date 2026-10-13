/-
# `Work.FTS.PhiStar.Honesty.radGreen_supp_weight_le`

The radial mode-`m` Green function of `Work.FTS.PhiStar.Radial.Defs`,
`radGreen α m c z = rgK·(z^{-q} ∫_0^z c t^{q-1} + z^{p} ∫_{Ioi z} c t^{-p-1})`
(`rgK = 1/(α(4m+5))`, `q = rgQ α m = (2m+5)/α`, `p = rgP α m = 2m/α`), obeys the weighted
support bound

  `|radGreen α m c z| ≤ C · M · z ^ (2/α) / (1+z) ^ (7/α)`

for a source `c` supported in `[a,b] ⊂ (0,∞)` (`0 < a ≤ b`), bounded by `M ≥ 0`, and `m ≥ 1`.

**Why the shape.**  The first term of the bracket is bounded by the *sharp* support estimate
`|∫_0^z c t^{q-1}| ≤ M·(min z b)^q/q`, the second by `|∫_{Ioi z} c t^{-p-1}| ≤ M·(max z a)^{-p}/p`;
additionally `∫_0^z c t^{q-1} = 0` for `z ≤ a` and `∫_{Ioi z} c t^{-p-1} = 0` for `b ≤ z`.  Three
regimes result, each producing one summand of the constant

  `C α a b = (1/2)·a^{-2/α}(1+a)^{7/α} + (1/14)·a^{-2/α}(1+b)^{7/α} + (1/63)·(1+b)^{7/α}b^{-2/α}`:

* `z ≤ a`: `|radGreen| ≤ rgK·z^p·(M a^{-p}/p) ≤ (1/2)·M·z^{2/α}a^{-2/α}`, because
  `rgK/p ≤ 1/18 ≤ 1/2` and `p ≥ 2/α` with `z/a ≤ 1` (`cmp1`);
* `a ≤ z ≤ b`: `|radGreen| ≤ rgK·M·(1/q + 1/p) ≤ M/14` and `z^{2/α}/(1+z)^{7/α} ≥ a^{2/α}/(1+b)^{7/α}`
  (`cmp2`);
* `b ≤ z`: `|radGreen| ≤ M·(rgK/q)·(b/z)^q ≤ (M/63)·(b/z)^{7/α}`, since `q ≥ 7/α` and `b/z ≤ 1`
  (`cmp3`).

The elementary integral estimates (`head_supp`, `tail_supp`, `head_zero`, `tail_zero`), the
arithmetic of `rgK, rgP, rgQ` (`RadGreenSupp.Consts`) and the three regime comparisons
(`cmp1`, `cmp2`, `cmp3`) are proved in the sibling modules of `RadGreenSupp/`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.Consts
import Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.head_supp
import Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.tail_supp
import Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.head_zero
import Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.tail_zero
import Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.cmp1
import Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.cmp2
import Submission.Work.FTS.PhiStar.Honesty.RadGreenSupp.cmp3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open MeasureTheory Set

namespace Work.FTS.PhiStar.Honesty

theorem radGreen_supp_weight_le {α : ℝ} (hα : 0 < α) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 ≤ M → ∀ {c : ℝ → ℝ},
      (∀ t : ℝ, t ∉ Set.Icc a b → c t = 0) → (∀ t : ℝ, |c t| ≤ M) →
      ∀ m : ℕ, 1 ≤ m → ∀ z : ℝ, 0 < z →
        |Work.FTS.PhiStar.Radial.radGreen α m c z|
          ≤ C * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) := by
  refine ⟨RadGreenSupp.C α a b, RadGreenSupp.C_pos hα ha hab, ?_⟩
  intro M hM c hsupp hb m hm z hz
  -- ### abbreviations
  set K : ℝ := Work.FTS.EllExist.rgK α m with hKdef
  set P : ℝ := Work.FTS.EllExist.rgP α m with hPdef
  set Q : ℝ := Work.FTS.EllExist.rgQ α m with hQdef
  have hKpos : 0 < K := by rw [hKdef]; exact Work.FTS.EllExist.rgK_pos hα m
  have hPpos : 0 < P := by rw [hPdef]; exact Work.FTS.EllExist.rgP_pos hα hm
  have hQpos : 0 < Q := by rw [hQdef]; exact Work.FTS.EllExist.rgQ_pos hα m
  have hzK : 0 < z ^ (-Q) := Real.rpow_pos_of_pos hz _
  have hzP : 0 < z ^ P := Real.rpow_pos_of_pos hz _
  -- ### the decomposition of `radGreen`
  have hrad : Work.FTS.PhiStar.Radial.radGreen α m c z
      = K * (z ^ (-Q) * Work.FTS.EllExist.rgA α m c z
              + z ^ P * Work.FTS.EllExist.rgB α m c z) := by
    rw [Work.FTS.EllExist.radGreen_eq, ← hKdef, ← hPdef, ← hQdef]
  -- ### the elementary triangle-inequality step
  have hmain : |Work.FTS.PhiStar.Radial.radGreen α m c z|
      ≤ K * (z ^ (-Q) * |Work.FTS.EllExist.rgA α m c z|
              + z ^ P * |Work.FTS.EllExist.rgB α m c z|) := by
    rw [hrad, abs_mul, abs_of_pos hKpos]
    refine mul_le_mul_of_nonneg_left ?_ hKpos.le
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_pos hzK, abs_of_pos hzP]
  -- ### the three regimes
  by_cases hza : z ≤ a
  · -- ## regime 1: `z ≤ a`
    have hAz : Work.FTS.EllExist.rgA α m c z = 0 := by
      have h := RadGreenSupp.head_zero (c := c) (a := a) (b := b)
        (e := Work.FTS.EllExist.rgQ α m - 1) (z := z) ha hab hsupp hz hza
      simpa only [Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgF1] using h
    have hBz : |Work.FTS.EllExist.rgB α m c z|
        ≤ M * a ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m := by
      have h := RadGreenSupp.tail_supp (c := c) (a := a) (b := b) (M := M)
        (p := Work.FTS.EllExist.rgP α m) (z := z) ha hab hM
        (Work.FTS.EllExist.rgP_pos hα hm) hsupp hb hz
      simpa only [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2, max_eq_right hza] using h
    calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
        ≤ K * (z ^ (-Q) * |Work.FTS.EllExist.rgA α m c z|
                + z ^ P * |Work.FTS.EllExist.rgB α m c z|) := hmain
      _ = K * (z ^ P * |Work.FTS.EllExist.rgB α m c z|) := by rw [hAz]; ring
      _ ≤ K * (z ^ P * (M * a ^ (-P) / P)) := by
          refine mul_le_mul_of_nonneg_left ?_ hKpos.le
          exact mul_le_mul_of_nonneg_left hBz hzP.le
      _ = Work.FTS.EllExist.rgK α m
            * (z ^ Work.FTS.EllExist.rgP α m
                * (M * a ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m)) := by
          rw [hKdef, hPdef]
      _ ≤ RadGreenSupp.C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) :=
          RadGreenSupp.cmp1 hα ha hab hM hm hz hza
  · by_cases hzb : z ≤ b
    · -- ## regime 2: `a ≤ z ≤ b`
      have haz : a ≤ z := le_of_not_ge hza
      have hA : |Work.FTS.EllExist.rgA α m c z|
          ≤ M * z ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m := by
        have h := RadGreenSupp.head_supp (c := c) (a := a) (b := b) (M := M)
          (e := Work.FTS.EllExist.rgQ α m - 1) (z := z) ha hab hM
          (by linarith [Work.FTS.EllExist.rgQ_pos hα m]) hsupp hb hz
        have hexp : (Work.FTS.EllExist.rgQ α m - 1) + 1 = Work.FTS.EllExist.rgQ α m := by ring
        simpa only [Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgF1, min_eq_left hzb, hexp] using h
      have hB : |Work.FTS.EllExist.rgB α m c z|
          ≤ M * z ^ (-(Work.FTS.EllExist.rgP α m)) / Work.FTS.EllExist.rgP α m := by
        have h := RadGreenSupp.tail_supp (c := c) (a := a) (b := b) (M := M)
          (p := Work.FTS.EllExist.rgP α m) (z := z) ha hab hM
          (Work.FTS.EllExist.rgP_pos hα hm) hsupp hb hz
        simpa only [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2, max_eq_left haz] using h
      calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
          ≤ K * (z ^ (-Q) * |Work.FTS.EllExist.rgA α m c z|
                  + z ^ P * |Work.FTS.EllExist.rgB α m c z|) := hmain
        _ ≤ K * (z ^ (-Q) * (M * z ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m)
                + z ^ P * (M * z ^ (-(Work.FTS.EllExist.rgP α m))
                    / Work.FTS.EllExist.rgP α m)) := by
            refine mul_le_mul_of_nonneg_left ?_ hKpos.le
            exact add_le_add (mul_le_mul_of_nonneg_left hA hzK.le)
              (mul_le_mul_of_nonneg_left hB hzP.le)
        _ = Work.FTS.EllExist.rgK α m
              * (z ^ (-(Work.FTS.EllExist.rgQ α m))
                    * (M * z ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m)
                  + z ^ Work.FTS.EllExist.rgP α m
                    * (M * z ^ (-(Work.FTS.EllExist.rgP α m))
                        / Work.FTS.EllExist.rgP α m)) := by
            rw [hKdef, hPdef, hQdef]
        _ ≤ RadGreenSupp.C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) :=
            RadGreenSupp.cmp2 hα ha hab hM hm hz haz hzb
    · -- ## regime 3: `b ≤ z`
      have hbz : b ≤ z := le_of_not_ge hzb
      have hBz : Work.FTS.EllExist.rgB α m c z = 0 := by
        have h := RadGreenSupp.tail_zero (c := c) (a := a) (b := b)
          (e := -(Work.FTS.EllExist.rgP α m) - 1) (z := z) ha hab hsupp hz hbz
        simpa only [Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2] using h
      have hAz : |Work.FTS.EllExist.rgA α m c z|
          ≤ M * b ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m := by
        have h := RadGreenSupp.head_supp (c := c) (a := a) (b := b) (M := M)
          (e := Work.FTS.EllExist.rgQ α m - 1) (z := z) ha hab hM
          (by linarith [Work.FTS.EllExist.rgQ_pos hα m]) hsupp hb hz
        have hexp : (Work.FTS.EllExist.rgQ α m - 1) + 1 = Work.FTS.EllExist.rgQ α m := by ring
        simpa only [Work.FTS.EllExist.rgA, Work.FTS.EllExist.rgF1, min_eq_right hbz, hexp] using h
      calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
          ≤ K * (z ^ (-Q) * |Work.FTS.EllExist.rgA α m c z|
                  + z ^ P * |Work.FTS.EllExist.rgB α m c z|) := hmain
        _ = K * (z ^ (-Q) * |Work.FTS.EllExist.rgA α m c z|) := by rw [hBz]; ring
        _ ≤ K * (z ^ (-Q) * (M * b ^ Work.FTS.EllExist.rgQ α m
              / Work.FTS.EllExist.rgQ α m)) := by
            refine mul_le_mul_of_nonneg_left ?_ hKpos.le
            exact mul_le_mul_of_nonneg_left hAz hzK.le
        _ = Work.FTS.EllExist.rgK α m
              * (z ^ (-(Work.FTS.EllExist.rgQ α m))
                  * (M * b ^ Work.FTS.EllExist.rgQ α m / Work.FTS.EllExist.rgQ α m)) := by
            rw [hKdef, hQdef]
        _ ≤ RadGreenSupp.C α a b * M * (z ^ (2 / α) / (1 + z) ^ (7 / α)) :=
            RadGreenSupp.cmp3 hα ha hab hM hm hz hbz

end Work.FTS.PhiStar.Honesty
