import Mathlib
import Submission.Work.Chen.SwitchDefs
import Submission.Commons.NumberTheory.Chen.vsieve_log_lower_sharp

namespace Work.NumberTheory.Chen

open Filter
open scoped BigOperators

/-- The two incarnations of the odd Euler product of the linear sieve agree. -/
private lemma VsieveOdd_eq_Vsieve (M : ℕ) :
    Commons.NumberTheory.Chen.ChenEight.VsieveOdd M = Commons.NumberTheory.Chen.Vsieve M := by
  have hset : Commons.NumberTheory.Chen.ChenEight.oddLt M
      = Commons.NumberTheory.Chen.oddPrimesLt M := by
    ext p
    simp only [Commons.NumberTheory.Chen.ChenEight.oddLt,
      Commons.NumberTheory.Chen.oddPrimesLt, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun h => by rw [h] at h3; norm_num at h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by have := h2.two_le; omega⟩
  rw [Commons.NumberTheory.Chen.ChenEight.VsieveOdd, Commons.NumberTheory.Chen.Vsieve, hset]

/-- `chenSiftLimitTenth x = ⌊x^{1/10}⌋₊ + 1`. -/
private lemma chenSiftLimitTenth_eq (x : ℕ) :
    Submission.chenSiftLimitTenth x = ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ + 1 := rfl

/-- `chenSiftLimitTenth x → ∞`. -/
private lemma eventually_le_chenSiftLimitTenth (Y : ℕ) :
    ∀ᶠ x : ℕ in Filter.atTop, Y ≤ Submission.chenSiftLimitTenth x := by
  have hpow : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 10)) Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hnat : Tendsto (fun x : ℕ => (x : ℝ) ^ ((1 : ℝ) / 10)) Filter.atTop Filter.atTop :=
    hpow.comp tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually_ge_atTop (((Y + 1 : ℕ) : ℝ)), eventually_ge_atTop 1]
    with x hx hx1
  have hfloor : Y + 1 ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 10)⌋₊ := Nat.le_floor hx
  rw [chenSiftLimitTenth_eq]
  omega

/-- `log (chenSiftLimitTenth x) ≤ (1/10)·log x + 1`. -/
private lemma log_chenSiftLimitTenth_le {x : ℕ} (hx : 1 ≤ x) :
    Real.log (Submission.chenSiftLimitTenth x : ℝ) ≤ (1 : ℝ) / 10 * Real.log (x : ℝ) + 1 := by
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hy1 : 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 10) := Real.one_le_rpow hx1R (by norm_num)
  have hypos : 0 < (x : ℝ) ^ ((1 : ℝ) / 10) := lt_of_lt_of_le zero_lt_one hy1
  have hfloor : (Submission.chenSiftLimitTenth x : ℝ)
      ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 10) := by
    rw [chenSiftLimitTenth_eq]
    push_cast
    have hfl := Nat.floor_le (le_of_lt hypos)
    linarith
  have hMpos : (0 : ℝ) < (Submission.chenSiftLimitTenth x : ℝ) := by
    have : 0 < Submission.chenSiftLimitTenth x := by
      rw [chenSiftLimitTenth_eq]
      exact Nat.succ_pos _
    exact_mod_cast this
  calc Real.log (Submission.chenSiftLimitTenth x : ℝ)
      ≤ Real.log (2 * (x : ℝ) ^ ((1 : ℝ) / 10)) := Real.log_le_log hMpos hfloor
    _ = Real.log 2 + ((1 : ℝ) / 10 * Real.log (x : ℝ)) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hypos), Real.log_rpow hx0]
    _ ≤ (1 : ℝ) / 10 * Real.log (x : ℝ) + 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith

theorem mertens_lower_tenth :
    ∀ᶠ x : ℕ in Filter.atTop,
      (34 / 5 : ℝ) * (x : ℝ)
        ≤ (x : ℝ) * Commons.NumberTheory.Chen.ChenEight.VsieveOdd (Submission.chenSiftLimitTenth x) * Real.log (x : ℝ) := by
  obtain ⟨Y₀, hY₀⟩ := Commons.NumberTheory.Chen.vsieve_log_lower_sharp
  have hlog : ∀ᶠ x : ℕ in Filter.atTop, (500 : ℝ) ≤ Real.log (x : ℝ) := by
    have h : Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact h.eventually_ge_atTop 500
  filter_upwards [eventually_le_chenSiftLimitTenth (max Y₀ 2), hlog, eventually_ge_atTop 1]
    with x hM hlogx hx1
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hlogxpos : 0 < Real.log (x : ℝ) := by linarith
  have hMY : Y₀ ≤ Submission.chenSiftLimitTenth x := le_trans (le_max_left _ _) hM
  have hM1 : 1 < Submission.chenSiftLimitTenth x := by
    have : 2 ≤ Submission.chenSiftLimitTenth x := le_trans (le_max_right _ _) hM
    omega
  have hlogMpos : 0 < Real.log (Submission.chenSiftLimitTenth x : ℝ) :=
    Real.log_pos (by exact_mod_cast hM1)
  have hV : (7 / 10 : ℝ)
      ≤ Commons.NumberTheory.Chen.ChenEight.VsieveOdd (Submission.chenSiftLimitTenth x)
        * Real.log (Submission.chenSiftLimitTenth x : ℝ) := by
    rw [VsieveOdd_eq_Vsieve]
    exact hY₀ _ hMY
  have hlogMb := log_chenSiftLimitTenth_le hx1
  have hnum : (34 / 5 : ℝ)
      ≤ Commons.NumberTheory.Chen.ChenEight.VsieveOdd (Submission.chenSiftLimitTenth x)
        * Real.log (x : ℝ) := by
    have h1 : (1 : ℝ) / 10 * Real.log (x : ℝ) + 1 ≤ (7 / 68) * Real.log (x : ℝ) := by
      nlinarith [hlogx]
    have hA : Real.log (x : ℝ) / ((1 : ℝ) / 10 * Real.log (x : ℝ) + 1)
        ≤ Real.log (x : ℝ) / Real.log (Submission.chenSiftLimitTenth x : ℝ) :=
      div_le_div_of_nonneg_left hlogxpos.le hlogMpos hlogMb
    have hB : (68 / 7 : ℝ)
        ≤ Real.log (x : ℝ) / ((1 : ℝ) / 10 * Real.log (x : ℝ) + 1) := by
      have hposb : 0 < (1 : ℝ) / 10 * Real.log (x : ℝ) + 1 := by linarith
      have h := div_le_div_of_nonneg_left hlogxpos.le hposb h1
      have heq : Real.log (x : ℝ) / ((7 / 68) * Real.log (x : ℝ)) = 68 / 7 := by
        field_simp
      linarith [heq ▸ h]
    have hstep2 : (34 / 5 : ℝ)
        ≤ (7 / 10) * (Real.log (x : ℝ) / Real.log (Submission.chenSiftLimitTenth x : ℝ)) := by
      have hBH := le_trans hB hA
      have hmul := mul_le_mul_of_nonneg_left hBH (by norm_num : (0 : ℝ) ≤ 7 / 10)
      have hc : (7 / 10 : ℝ) * (68 / 7) = 34 / 5 := by norm_num
      linarith [hmul]
    have hstep1 : (7 / 10) * (Real.log (x : ℝ) / Real.log (Submission.chenSiftLimitTenth x : ℝ))
        ≤ Commons.NumberTheory.Chen.ChenEight.VsieveOdd (Submission.chenSiftLimitTenth x)
          * Real.log (x : ℝ) := by
      have hxdiv : 0 ≤ Real.log (x : ℝ) / Real.log (Submission.chenSiftLimitTenth x : ℝ) :=
        div_nonneg hlogxpos.le hlogMpos.le
      have h := mul_le_mul_of_nonneg_right hV hxdiv
      calc (7 / 10) * (Real.log (x : ℝ) / Real.log (Submission.chenSiftLimitTenth x : ℝ))
          ≤ (Commons.NumberTheory.Chen.ChenEight.VsieveOdd (Submission.chenSiftLimitTenth x)
              * Real.log (Submission.chenSiftLimitTenth x : ℝ))
            * (Real.log (x : ℝ) / Real.log (Submission.chenSiftLimitTenth x : ℝ)) := h
        _ = Commons.NumberTheory.Chen.ChenEight.VsieveOdd (Submission.chenSiftLimitTenth x)
              * Real.log (x : ℝ) := by
            field_simp
    linarith
  have hfinal : (34 / 5 : ℝ) * (x : ℝ)
      ≤ (x : ℝ) * Commons.NumberTheory.Chen.ChenEight.VsieveOdd (Submission.chenSiftLimitTenth x)
        * Real.log (x : ℝ) := by
    rw [show (x : ℝ) * Commons.NumberTheory.Chen.ChenEight.VsieveOdd (Submission.chenSiftLimitTenth x)
          * Real.log (x : ℝ)
        = (Commons.NumberTheory.Chen.ChenEight.VsieveOdd (Submission.chenSiftLimitTenth x)
            * Real.log (x : ℝ)) * (x : ℝ) from by ring]
    exact mul_le_mul_of_nonneg_right hnum hx0.le
  exact hfinal

end Work.NumberTheory.Chen
