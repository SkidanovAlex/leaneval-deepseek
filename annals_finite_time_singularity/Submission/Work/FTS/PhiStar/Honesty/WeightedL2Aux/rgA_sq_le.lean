import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.WeightedL2Aux.cs
import Submission.Work.FTS.PhiStar.Honesty.rgF1_integrableOn_Ioc
import Submission.Work.FTS.PhiStar.Honesty.sq_intervalIntegral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real

namespace Work.FTS.PhiStar.Honesty.WeightedL2Aux

set_option autoImplicit false

local notation "rgQ" => Work.FTS.EllExist.rgQ
local notation "rgF1" => Work.FTS.EllExist.rgF1
local notation "rgA" => Work.FTS.EllExist.rgA

/-- `(a/t²)² = a²/t⁴`, for every `t` (both sides vanish at `t = 0`). -/
private lemma div_sq_sq (a t : ℝ) : (a / t ^ 2) ^ 2 = a ^ 2 / t ^ 4 := by
  rw [div_pow]; ring_nf

/-- `(a/t²)·t^{q+1} = a·t^{q-1}` for `t > 0`. -/
private lemma div_sq_mul_rpow (a q t : ℝ) (ht : 0 < t) :
    (a / t ^ 2) * t ^ (q + 1) = a * t ^ (q - 1) := by
  have h : t ^ 2 = t ^ (2 : ℝ) := (Real.rpow_natCast t 2).symm
  rw [h, div_eq_mul_inv, mul_assoc, ← Real.rpow_neg (le_of_lt ht) 2, ← Real.rpow_add ht]
  congr 1; ring_nf

/-- `(t^{q+1})² = t^{2q+2}` for `t > 0`. -/
private lemma rpow_add_one_sq (q t : ℝ) (ht : 0 < t) :
    (t ^ (q + 1)) ^ 2 = t ^ (2 * q + 2) := by
  have h1 : (t ^ (q + 1)) ^ 2 = (t ^ (q + 1)) ^ (2 : ℝ) :=
    (Real.rpow_natCast (t ^ (q + 1)) 2).symm
  have h2 : (t ^ (q + 1)) ^ (2 : ℝ) = t ^ ((q + 1) * (2 : ℝ)) :=
    (Real.rpow_mul ht.le (q + 1) (2 : ℝ)).symm
  rw [h1, h2]; congr 1; ring

theorem rgA_sq_le {α : ℝ} {m : ℕ} {d : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hd : AEMeasurable d)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2) (Set.Ioi 1))
    {z : ℝ} (hz : 0 < z) :
    (Work.FTS.EllExist.rgA α m d z) ^ 2
      ≤ ((∫ t in Set.Ioo (0:ℝ) 1, (d t) ^ 2 / t ^ 4)
          + (∫ t in Set.Ioi (1:ℝ), (d t) ^ 2)) * (z ^ (2 * Work.FTS.EllExist.rgQ α m + 3) / (2 * Work.FTS.EllExist.rgQ α m + 3)) := by
  have hq28 : 28 ≤ rgQ α m := Work.FTS.EllExist.rgQ_ge hα hα4 hm
  set A : ℝ := ∫ t in Set.Ioo (0:ℝ) 1, (d t) ^ 2 / t ^ 4 with hAdef
  set B : ℝ := ∫ t in Set.Ioi (1:ℝ), (d t) ^ 2 with hBdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards with t
    positivity
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards with t
    positivity
  -- the near-field weight is integrable on `(0,1]` and on `(1,z]`
  have hnear01 : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioc (0:ℝ) 1) :=
    hnear.congr_set_ae (Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := 1)).symm
  have hfar1z : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioc (1:ℝ) z) := by
    have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2) (Set.Ioc (1:ℝ) z) :=
      hfar.mono_set (fun x hx => hx.1)
    have haesm : AEStronglyMeasurable (fun t : ℝ => (d t) ^ 2 / t ^ 4)
        (volume.restrict (Set.Ioc (1:ℝ) z)) :=
      (((hd.pow_const 2).div (aemeasurable_id.pow_const 4)).restrict
        (s := Set.Ioc (1:ℝ) z)).aestronglyMeasurable
    refine MeasureTheory.Integrable.mono' hbase haesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht4 : (0:ℝ) < t ^ 4 := by
      have : (0:ℝ) < t := lt_trans one_pos ht.1
      positivity
    have ht4one : (1:ℝ) ≤ t ^ 4 := one_le_pow₀ (n := 4) ht.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ ht4]
    nlinarith [sq_nonneg (d t), ht4one]
  -- integrability of the near-field weight on the whole `(0,z]`
  have hne_int : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioc (0:ℝ) z) := by
    rcases le_or_gt z 1 with hz1 | hz1
    · have h : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2 / t ^ 4) (Set.Ioo (0:ℝ) z) :=
        hnear.mono_set (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hz1⟩)
      exact h.congr_set_ae (Ioo_ae_eq_Ioc (a := (0:ℝ)) (b := z)).symm
    · rw [← Set.Ioc_union_Ioc_eq_Ioc zero_le_one hz1.le]
      exact hnear01.union hfar1z
  -- the value of the near-field integral is at most `A + B`
  have hInt_le : (∫ t in Set.Ioc (0:ℝ) z, (d t) ^ 2 / t ^ 4) ≤ A + B := by
    rcases le_or_gt z 1 with hz1 | hz1
    · have h2 : (∫ t in Set.Ioo (0:ℝ) z, (d t) ^ 2 / t ^ 4) ≤ A := by
        rw [hAdef]
        refine MeasureTheory.setIntegral_mono_set hnear ?_ ?_
        · filter_upwards with x; positivity
        · filter_upwards with x hx
          exact ⟨hx.1, lt_of_lt_of_le hx.2 hz1⟩
      rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
      linarith
    · have hdisj : Disjoint (Set.Ioc (0:ℝ) 1) (Set.Ioc (1:ℝ) z) := by
        rw [Set.disjoint_left]
        rintro x hx1 hx2
        linarith [hx1.2, hx2.1]
      rw [← Set.Ioc_union_Ioc_eq_Ioc zero_le_one hz1.le,
        MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hnear01 hfar1z]
      have hEq1 : (∫ t in Set.Ioc (0:ℝ) 1, (d t) ^ 2 / t ^ 4) = A := by
        rw [hAdef, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      have hle2 : (∫ t in Set.Ioc (1:ℝ) z, (d t) ^ 2 / t ^ 4) ≤ B := by
        have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => (d t) ^ 2) (Set.Ioc (1:ℝ) z) :=
          hfar.mono_set (fun x hx => hx.1)
        have hm1 : (∫ t in Set.Ioc (1:ℝ) z, (d t) ^ 2 / t ^ 4) ≤
            ∫ t in Set.Ioc (1:ℝ) z, (d t) ^ 2 := by
          refine MeasureTheory.setIntegral_mono_on hfar1z hbase measurableSet_Ioc ?_
          intro t ht
          have ht4 : (0:ℝ) < t ^ 4 := by
            have : (0:ℝ) < t := lt_trans one_pos ht.1
            positivity
          have ht4one : (1:ℝ) ≤ t ^ 4 := one_le_pow₀ (n := 4) ht.1.le
          rw [div_le_iff₀ ht4]
          nlinarith [sq_nonneg (d t), ht4one]
        have hm2 : (∫ t in Set.Ioc (1:ℝ) z, (d t) ^ 2) ≤ B := by
          rw [hBdef]
          refine MeasureTheory.setIntegral_mono_set hfar ?_ ?_
          · filter_upwards with x; positivity
          · filter_upwards with x hx; exact hx.1
        linarith
      linarith
  -- Cauchy–Schwarz on `0..z`
  have hF1int : IntervalIntegrable (rgF1 α m d) volume (0:ℝ) z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mpr
      (Work.FTS.PhiStar.Honesty.rgF1_integrableOn_Ioc hα hα4 hm hd hnear hfar z hz)
  have hf2 : IntervalIntegrable (fun t : ℝ => (d t / t ^ 2) ^ 2) volume (0:ℝ) z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mpr
      (hne_int.congr_fun (fun t _ => (div_sq_sq (d t) t).symm) measurableSet_Ioc)
  have hg2 : IntervalIntegrable (fun t : ℝ => (t ^ (rgQ α m + 1)) ^ 2) volume (0:ℝ) z := by
    refine IntervalIntegrable.congr ?_
      (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := z)
        (r := 2 * rgQ α m + 2) (by linarith))
    intro t ht
    rw [Set.uIoc_of_le hz.le] at ht
    exact (rpow_add_one_sq (rgQ α m) t ht.1).symm
  have hfg : IntervalIntegrable (fun t : ℝ => (d t / t ^ 2) * t ^ (rgQ α m + 1)) volume (0:ℝ) z := by
    refine IntervalIntegrable.congr ?_ hF1int
    intro t ht
    rw [Set.uIoc_of_le hz.le] at ht
    show rgF1 α m d t = (d t / t ^ 2) * t ^ (rgQ α m + 1)
    rw [Work.FTS.EllExist.rgF1]
    exact (div_sq_mul_rpow (d t) (rgQ α m) t ht.1).symm
  have hcs := Work.FTS.PhiStar.Honesty.sq_intervalIntegral_mul_le hz.le hf2 hg2 hfg
  have hLHS : (∫ t in (0:ℝ)..z, (d t / t ^ 2) * t ^ (rgQ α m + 1)) = rgA α m d z := by
    show (∫ t in (0:ℝ)..z, (d t / t ^ 2) * t ^ (rgQ α m + 1)) = ∫ t in (0:ℝ)..z, rgF1 α m d t
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with t ht
    rw [Set.uIoc_of_le hz.le] at ht
    rw [Work.FTS.EllExist.rgF1]
    exact div_sq_mul_rpow (d t) (rgQ α m) t ht.1
  have hI1 : (∫ t in (0:ℝ)..z, (d t / t ^ 2) ^ 2)
      = ∫ t in Set.Ioc (0:ℝ) z, (d t) ^ 2 / t ^ 4 := by
    rw [intervalIntegral.integral_of_le hz.le]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => div_sq_sq (d t) t)
  have hI2 : (∫ t in (0:ℝ)..z, (t ^ (rgQ α m + 1)) ^ 2)
      = z ^ (2 * rgQ α m + 3) / (2 * rgQ α m + 3) := by
    have hbase := integral_rpow (a := (0:ℝ)) (b := z) (r := 2 * rgQ α m + 2) (Or.inl (by linarith))
    have hcong : (∫ t in (0:ℝ)..z, (t ^ (rgQ α m + 1)) ^ 2)
        = ∫ t in (0:ℝ)..z, t ^ (2 * rgQ α m + 2) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with t ht
      rw [Set.uIoc_of_le hz.le] at ht
      exact rpow_add_one_sq (rgQ α m) t ht.1
    rw [hcong, hbase,
      show 2 * rgQ α m + 2 + 1 = 2 * rgQ α m + 3 from by ring,
      Real.zero_rpow (by linarith : (2 * rgQ α m + 3 : ℝ) ≠ 0)]
    ring
  calc (rgA α m d z) ^ 2
      = (∫ t in (0:ℝ)..z, (d t / t ^ 2) * t ^ (rgQ α m + 1)) ^ 2 := by rw [hLHS]
    _ ≤ (∫ t in (0:ℝ)..z, (d t / t ^ 2) ^ 2)
          * (∫ t in (0:ℝ)..z, (t ^ (rgQ α m + 1)) ^ 2) := hcs
    _ = (∫ t in Set.Ioc (0:ℝ) z, (d t) ^ 2 / t ^ 4)
          * (z ^ (2 * rgQ α m + 3) / (2 * rgQ α m + 3)) := by rw [hI1, hI2]
    _ ≤ (A + B) * (z ^ (2 * rgQ α m + 3) / (2 * rgQ α m + 3)) :=
        mul_le_mul_of_nonneg_right hInt_le (by positivity)
    _ = ((∫ t in Set.Ioo (0:ℝ) 1, (d t) ^ 2 / t ^ 4)
          + (∫ t in Set.Ioi (1:ℝ), (d t) ^ 2)) * (z ^ (2 * rgQ α m + 3) / (2 * rgQ α m + 3)) := by
        rw [hAdef, hBdef]

end Work.FTS.PhiStar.Honesty.WeightedL2Aux
