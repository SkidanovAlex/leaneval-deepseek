import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `majorant_tail`: the tail bound for `s ↦ s^{1/2}/(1+s)²`

For every `z > 0` the function `maj s = s ^ (1/2) / (1 + s) ^ 2` is integrable on `(z, ∞)`
and its tail integral is at most `3`.

The tail integral is actually convergent as `z → 0⁺` with value `π/2 ≈ 1.571`, but only the
crude constant `3` is needed.  The proof splits the halfline at `1`:

* `maj s ≤ s ^ (-3/2)` for `s ≥ 1`, and `∫_1^∞ s^{-3/2} = 2`;
* `maj s ≤ s ^ (1/2)` for `0 < s ≤ 1`, and `∫_z^1 s^{1/2} = (2/3)(1 - z^{3/2}) ≤ 2/3`.

Hence `∫_z^∞ maj ≤ 2/3 + 2 = 8/3 ≤ 3`.  The two pieces are glued by
`intervalIntegral.integral_interval_add_Ioi'` (`∫_z^1 + ∫_1^∞ = ∫_z^∞`, valid for *every*
`z`, so no case distinction is needed in the glueing step), and the integrability on
`(z, ∞)` follows from `(z,∞) ⊆ (z,1] ∪ (1,∞)` together with `IntegrableOn.union`.
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

/-- The integrand `s^{1/2}/(1+s)²` of the tail majorant. -/
private noncomputable def maj (s : ℝ) : ℝ := s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2

/-- `maj` is continuous on the open halfline `(0,∞)`. -/
private lemma maj_cont : ContinuousOn maj (Ioi 0) := by
  have hfe : maj = fun s : ℝ => Real.sqrt s / (1 + s) ^ 2 := by
    funext s; simp only [maj, Real.sqrt_eq_rpow]
  rw [hfe]
  refine ContinuousOn.div Real.continuous_sqrt.continuousOn ?_ (fun x hx => ?_)
  · exact ((continuous_const.add continuous_id).pow 2).continuousOn
  · have hx0 : 0 < x := hx
    positivity

/-- `s ↦ s^{1/2}` is continuous on `(0,∞)`. -/
private lemma sqr_cont : ContinuousOn (fun s : ℝ => s ^ ((1 : ℝ) / 2)) (Ioi 0) := by
  have hfe : (fun s : ℝ => s ^ ((1 : ℝ) / 2)) = fun s : ℝ => Real.sqrt s := by
    funext s; rw [Real.sqrt_eq_rpow]
  rw [hfe]; exact Real.continuous_sqrt.continuousOn

private lemma maj_cont_uIcc {z : ℝ} (hz : 0 < z) : ContinuousOn maj (uIcc z 1) :=
  maj_cont.mono (by intro s hs; exact lt_of_lt_of_le (lt_min hz zero_lt_one) hs.1)

private lemma sqr_cont_uIcc {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun s : ℝ => s ^ ((1 : ℝ) / 2)) (uIcc z 1) :=
  sqr_cont.mono (by intro s hs; exact lt_of_lt_of_le (lt_min hz zero_lt_one) hs.1)

/-- Pointwise domination on `(1,∞)`: `maj s ≤ s ^ (-3/2)`. -/
private lemma maj_le_rpow_neg {a : ℝ} (ha : (1 : ℝ) < a) :
    maj a ≤ a ^ (-(3 : ℝ) / 2) := by
  have ha1 : 0 < a := by linarith
  have hle : a ^ 2 ≤ (1 + a) ^ 2 := by
    have h1 : (0 : ℝ) ≤ a := le_of_lt ha1
    have h2 : a ≤ 1 + a := by linarith
    exact pow_le_pow_left₀ h1 h2 2
  have h := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ a ^ ((1 : ℝ) / 2))
    (by positivity : (0 : ℝ) < a ^ 2) hle
  simp only [maj]
  refine le_trans h ?_
  rw [show (-(3 : ℝ) / 2) = (1 : ℝ) / 2 - 2 by norm_num, ← Real.rpow_natCast a 2]
  exact le_of_eq (Real.rpow_sub ha1 (1 / 2) 2).symm

/-- `maj` is integrable on `(1,∞)`. -/
private lemma maj_int_one : IntegrableOn maj (Ioi 1) := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hcont : ContinuousOn maj (Ioi 1) :=
    maj_cont.mono (by intro s hs; exact lt_trans zero_lt_one (mem_Ioi.mp hs))
  refine hbase.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  have ha1 : 0 < a := by linarith [mem_Ioi.mp ha]
  have hnn : (0 : ℝ) ≤ a ^ ((1 : ℝ) / 2) / (1 + a) ^ 2 :=
    div_nonneg (Real.rpow_nonneg ha1.le _) (sq_nonneg _)
  have hle := maj_le_rpow_neg (mem_Ioi.mp ha)
  simp only [maj]
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hle

/-- `∫_1^∞ maj ≤ 2`. -/
private lemma maj_val_one : ∫ s in Ioi (1 : ℝ), maj s ≤ 2 := by
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hb : ∫ t in Ioi (1 : ℝ), t ^ (-(3 : ℝ) / 2) = 2 := by
    rw [integral_Ioi_rpow_of_lt (a := -(3 : ℝ) / 2) (c := 1) (by norm_num) (by norm_num)]
    norm_num
  have hmono := setIntegral_mono_ae_restrict maj_int_one hbase (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact maj_le_rpow_neg (mem_Ioi.mp ha))
  rw [hb] at hmono
  exact hmono

/-- `∫_z^1 maj ≤ 2/3` for every `z > 0`. -/
private lemma maj_interval_le {z : ℝ} (hz : 0 < z) : ∫ s in z..1, maj s ≤ 2 / 3 := by
  by_cases h : z ≤ 1
  · have hmono := intervalIntegral.integral_mono_on h
      ((maj_cont_uIcc hz).intervalIntegrable (μ := volume))
      ((sqr_cont_uIcc hz).intervalIntegrable (μ := volume)) (fun x hx => by
        have hx0 : 0 < x := lt_of_lt_of_le hz hx.1
        have h1x : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith [hx0]
        simp only [maj]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + x) ^ 2)]
        exact le_mul_of_one_le_right (by positivity) h1x)
    have hval : ∫ x in z..1, x ^ ((1 : ℝ) / 2) = (1 - z ^ ((3 : ℝ) / 2)) / ((3 : ℝ) / 2) := by
      rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2)), Real.one_rpow]
      norm_num
    rw [hval] at hmono
    have hz32 : (0 : ℝ) ≤ z ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hz.le _
    linarith
  · push Not at h
    rw [intervalIntegral.integral_symm (a := 1) (b := z)]
    have hnn : 0 ≤ ∫ x in 1..z, maj x :=
      intervalIntegral.integral_nonneg h.le (fun u hu => by
        have hu0 : (0 : ℝ) < u := by linarith [hu.1]
        have hnum : (0 : ℝ) ≤ u ^ ((1 : ℝ) / 2) / (1 + u) ^ 2 :=
          div_nonneg (Real.rpow_nonneg hu0.le _) (sq_nonneg _)
        simpa only [maj] using hnum)
    linarith

/-- `maj` is integrable on `(z,∞)` for `z > 0`. -/
private lemma maj_int_Ioi {z : ℝ} (hz : 0 < z) : IntegrableOn maj (Ioi z) := by
  have hii : IntervalIntegrable maj volume z 1 := (maj_cont_uIcc hz).intervalIntegrable
  have hU : IntegrableOn maj (Ioc z 1 ∪ Ioi 1) := hii.1.union maj_int_one
  refine hU.mono_set ?_
  intro s hs
  by_cases hs1 : s ≤ 1
  · exact Or.inl ⟨mem_Ioi.mp hs, hs1⟩
  · exact Or.inr (lt_of_not_ge hs1)

theorem majorant_tail {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) (Set.Ioi z) ∧
      ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ 3 := by
  have hii : IntervalIntegrable maj volume z 1 := (maj_cont_uIcc hz).intervalIntegrable
  have hdec := intervalIntegral.integral_interval_add_Ioi' hii maj_int_one
  have hz1 : ∫ s in z..1, maj s ≤ 2 / 3 := maj_interval_le hz
  have hone : ∫ s in Ioi (1 : ℝ), maj s ≤ 2 := maj_val_one
  have hint : IntegrableOn maj (Ioi z) := maj_int_Ioi hz
  have hcalc : ∫ s in Ioi z, maj s ≤ 3 := by linarith
  exact ⟨hint, hcalc⟩

end Work.FTS_RegExport.RXT.Sys.L12FKaux
