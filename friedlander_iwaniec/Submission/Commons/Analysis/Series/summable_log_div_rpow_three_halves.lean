import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SumIntegralComparisons

open Set MeasureTheory intervalIntegral Filter
open scoped Topology

namespace Commons.Analysis.Series

/-- The summand `log x / x ^ (3/2)`. -/
private noncomputable abbrev logDivRpow3 (x : ℝ) : ℝ := Real.log x / x ^ ((3 : ℝ) / 2)

/-- `log x / x ^ (3/2)` is antitone on `[3, ∞)`. -/
private lemma logDivRpow3_antitone : AntitoneOn logDivRpow3 (Ici (3:ℝ)) := by
  have hanti := Real.log_div_self_rpow_antitoneOn (a := (3:ℝ)/2) (by norm_num)
  have hexp : Real.exp (((3:ℝ)/2))⁻¹ ≤ 3 := by
    have h1 : Real.exp (((3:ℝ)/2))⁻¹ < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
    linarith [Real.exp_one_lt_three]
  intro x hx y hy hxy
  exact hanti (le_trans hexp hx) (le_trans hexp hy) hxy

/-- `log x / x ^ (3/2)` is nonnegative on `(3, ∞)`. -/
private lemma logDivRpow3_nonneg : ∀ x ∈ Ioi (3:ℝ), 0 ≤ logDivRpow3 x := by
  intro x hx
  have hx3 : (3:ℝ) < x := hx
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hx0 : (0:ℝ) < x := by linarith
  exact div_nonneg hlog (Real.rpow_nonneg hx0.le _)

/-- An antiderivative of `log x / x ^ (3/2)`: `-2 (log x + 2) / sqrt x`. -/
private lemma hasDerivAt_logDivRpow3_prim (x : ℝ) (hx : x ∈ Ici (3:ℝ)) :
    HasDerivAt (fun y : ℝ => -((2 * Real.log y + 4) / Real.sqrt y)) (logDivRpow3 x) x := by
  have hx3 : (3:ℝ) ≤ x := hx
  have hxpos : (0:ℝ) < x := by linarith
  have hx0 : x ≠ 0 := hxpos.ne'
  have hs0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hxpos).ne'
  have hnum : HasDerivAt (fun y : ℝ => 2 * Real.log y + 4) (2 * x⁻¹) x := by
    simpa using ((Real.hasDerivAt_log hx0).const_mul 2).add_const 4
  have hden : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hx0
  have hq := hnum.div hden hs0
  have hn := hq.neg
  have h32 : x ^ ((3:ℝ)/2) = x * Real.sqrt x := by
    have hsp : ((3:ℝ)/2) = 1 + 1/2 := by norm_num
    rw [hsp, Real.rpow_add hxpos, Real.rpow_one, Real.sqrt_eq_rpow]
  have hval : -((2 * x⁻¹ * Real.sqrt x - (2 * Real.log x + 4) * (1 / (2 * Real.sqrt x)))
        / (Real.sqrt x) ^ 2) = logDivRpow3 x := by
    rw [logDivRpow3, h32]
    set s := Real.sqrt x with hs
    have hs_ne : s ≠ 0 := by rw [hs]; exact hs0
    have hs_sq : s ^ 2 = x := by rw [hs]; exact Real.sq_sqrt hxpos.le
    rw [← hs_sq]
    field_simp
    ring
  rwa [hval] at hn

/-- The antiderivative tends to `0` at `+∞`. -/
private lemma tendsto_logDivRpow3_prim :
    Tendsto (fun y : ℝ => -((2 * Real.log y + 4) / Real.sqrt y)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => Real.log y / y ^ ((1:ℝ)/2)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun y : ℝ => (Real.sqrt y)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_sqrt_atTop.inv_tendsto_atTop
  have h3 : Tendsto (fun y : ℝ => 2 * (Real.log y / y ^ ((1:ℝ)/2)) + 4 * (Real.sqrt y)⁻¹)
      atTop (𝓝 0) := by
    simpa using (h1.const_mul 2).add (h2.const_mul 4)
  have h4 : Tendsto (fun y : ℝ => -(2 * (Real.log y / y ^ ((1:ℝ)/2)) + 4 * (Real.sqrt y)⁻¹))
      atTop (𝓝 0) := by simpa using h3.neg
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  have hy0 : y ≠ 0 := hy.ne'
  have hs_ne : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  rw [Real.sqrt_eq_rpow]
  field_simp

/-- The improper integral of `log x / x ^ (3/2)` over `(3, ∞)`. -/
private lemma integral_logDivRpow3 :
    ∫ x in Ioi (3:ℝ), logDivRpow3 x = (2 * Real.log 3 + 4) / Real.sqrt 3 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun y : ℝ => -((2 * Real.log y + 4) / Real.sqrt y)) (g' := logDivRpow3) (a := (3:ℝ)) (l := 0)
    hasDerivAt_logDivRpow3_prim logDivRpow3_nonneg tendsto_logDivRpow3_prim
  rw [h]
  ring

/-- `log x / x ^ (3/2)` is integrable on `(3, ∞)`. -/
private lemma integrableOn_logDivRpow3 : IntegrableOn logDivRpow3 (Ioi (3:ℝ)) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (g := fun y : ℝ => -((2 * Real.log y + 4) / Real.sqrt y)) (g' := logDivRpow3) (a := (3:ℝ)) (l := 0)
    hasDerivAt_logDivRpow3_prim logDivRpow3_nonneg tendsto_logDivRpow3_prim

theorem summable_log_div_rpow_three_halves :
    Summable (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2)) ∧
      (∑' n : ℕ, Real.log (n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2)) ≤ 20 := by
  have hsummable : Summable (fun n : ℕ => logDivRpow3 n) :=
    AntitoneOn.summable_of_integrableOn_Ioi (N := 3)
      logDivRpow3_antitone integrableOn_logDivRpow3 logDivRpow3_nonneg
  have hanti' : AntitoneOn logDivRpow3 (Ici (((4:ℕ):ℝ) - 1)) := by
    rw [show (((4:ℕ):ℝ) - 1) = 3 by norm_num]; exact logDivRpow3_antitone
  have hint' : IntegrableOn logDivRpow3 (Ioi (((4:ℕ):ℝ) - 1)) := by
    rw [show (((4:ℕ):ℝ) - 1) = 3 by norm_num]; exact integrableOn_logDivRpow3
  have hnonneg' : ∀ t ∈ Ioi (((4:ℕ):ℝ) - 1), 0 ≤ logDivRpow3 t := by
    intro t ht
    rw [show (((4:ℕ):ℝ) - 1) = 3 by norm_num] at ht
    exact logDivRpow3_nonneg t ht
  have hb := AntitoneOn.abs_tsum_sub_sum_range_le_integral (f := logDivRpow3) (N := 4)
    (by norm_num) hanti' hint' hnonneg'
  rw [show (((4:ℕ):ℝ) - 1) = 3 by norm_num, integral_logDivRpow3] at hb
  have hint_le : (2 * Real.log 3 + 4) / Real.sqrt 3 ≤ 5 := by
    have hlog3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
      linarith
    have hnum : 2 * Real.log 3 + 4 ≤ 8 := by linarith
    have hden : (8:ℝ)/5 ≤ Real.sqrt 3 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hposden : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    calc (2 * Real.log 3 + 4) / Real.sqrt 3 ≤ 8 / Real.sqrt 3 :=
          div_le_div_of_nonneg_right hnum hposden.le
      _ ≤ 8 / ((8:ℝ)/5) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
      _ = 5 := by norm_num
  have hpartial : ∑ n ∈ Finset.range 4, logDivRpow3 n ≤ 4 := by
    have hle : ∀ n ∈ Finset.range 4, logDivRpow3 n ≤ 1 := by
      intro n hn
      simp only [Finset.mem_range] at hn
      interval_cases n
      · simp [logDivRpow3]
      · simp [logDivRpow3]
      · have h1 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
        have h2 : (1:ℝ) ≤ 2 ^ ((3:ℝ)/2) := Real.one_le_rpow (by norm_num) (by norm_num)
        rw [logDivRpow3, div_le_one (Real.rpow_pos_of_pos (by norm_num) _)]
        linarith
      · have h1 : Real.log 3 ≤ 2 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3); linarith
        have h2 : (2:ℝ) ≤ 3 ^ ((3:ℝ)/2) := by
          have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
            (by norm_num : (1:ℝ) ≤ (3:ℝ)/2)
          rw [Real.rpow_one] at h
          linarith
        rw [logDivRpow3, div_le_one (Real.rpow_pos_of_pos (by norm_num) _)]
        exact le_trans h1 h2
    calc ∑ n ∈ Finset.range 4, logDivRpow3 n ≤ ∑ n ∈ Finset.range 4, (1:ℝ) :=
          Finset.sum_le_sum hle
      _ = 4 := by simp
  refine ⟨?_, ?_⟩
  · simpa [logDivRpow3] using hsummable
  · have hkey := (abs_le.mp (le_trans hb hint_le)).2
    have : (∑' n : ℕ, logDivRpow3 n) ≤ 20 := by linarith
    simpa [logDivRpow3] using this

end Commons.Analysis.Series
