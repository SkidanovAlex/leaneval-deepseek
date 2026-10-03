import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.BpWinDefs
import Submission.Work.FITop.RCPrelude

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIChain

open scoped BigOperators

noncomputable section

/-- Numeric lower bound for the Rankin exponent: `2^40 · log 2 / 2 ≥ 262150`. -/
lemma RhoTailRankin_num : (262150 : ℝ) ≤ (2 : ℝ) ^ 40 * Real.log 2 / 2 := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    refine (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)).mpr ?_
    have h2e : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 / 2)]
  have hnum : (262150 : ℝ) ≤ (2 : ℝ) ^ 39 * (1 / 2) := by norm_num
  have h39 : (2 : ℝ) ^ 39 * (1 / 2) ≤ (2 : ℝ) ^ 40 * Real.log 2 / 2 := by
    have he : (2 : ℝ) ^ 40 * Real.log 2 / 2 = (2 : ℝ) ^ 39 * Real.log 2 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hlog2 (by positivity)
  linarith

/-- The `Pzc`-cutoff data feeding the Rankin exponent: `log Pzc x` lies between
`(loglog x)²` and `2 (loglog x)²` for all large `x`. -/
lemma RhoTailRankin_PzFacts :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      2 ≤ Pzc x ∧
      (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pzc x : ℝ) ∧
      Real.log (Pzc x : ℝ) ≤ 2 * (Real.log (Real.log (x : ℝ))) ^ 2 := by
  refine ⟨10 ^ 50, ?_⟩
  intro x hx
  have hxR : (10 : ℝ) ^ 50 ≤ (x : ℝ) := by exact_mod_cast hx
  have hPzeq : Pzc x = Work.FITop.Pcut x := rfl
  have hlogx100 : 100 ≤ Real.log (x : ℝ) := by
    have h1 : Real.log ((10 : ℝ) ^ 50) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by positivity) hxR
    have h2 : Real.log ((10 : ℝ) ^ 50) = 50 * Real.log 10 := by
      rw [Real.log_pow]; norm_num
    have hlog10 : (2 : ℝ) ≤ Real.log 10 := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 10)).mpr ?_
      have h2e : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    linarith
  have ht4 : 4 ≤ Real.log (Real.log (x : ℝ)) := by
    have hlog100 : (4 : ℝ) ≤ Real.log 100 := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 100)).mpr ?_
      have h2 : Real.exp (2 : ℝ) ≤ 10 := by
        have h2e : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
      have h4 : Real.exp (4 : ℝ) = Real.exp 2 ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h4]; nlinarith [h2, Real.exp_pos 2]
    exact le_trans hlog100 (Real.log_le_log (by norm_num) hlogx100)
  have ht2 : (16 : ℝ) ≤ (Real.log (Real.log (x : ℝ))) ^ 2 := by nlinarith
  have hlo := Work.FITop.FI_log_Pcut_ge x
  have hhi := Work.FITop.FI_log_Pcut_le x
  have hlog2le : Real.log 2 ≤ (Real.log (Real.log (x : ℝ))) ^ 2 := by
    have h1 : Real.log 2 ≤ 1 := by
      have h' := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    linarith
  refine ⟨?_, hlo, ?_⟩
  · rw [hPzeq]
    have hpos : 0 < (Work.FITop.Pcut x : ℝ) := Work.FITop.FI_Pcut_pos x
    have hlog2lo : Real.log 2 ≤ Real.log (Work.FITop.Pcut x : ℝ) := le_trans hlog2le hlo
    exact_mod_cast (Real.log_le_log_iff (by norm_num : (0 : ℝ) < 2) hpos).mp hlog2lo
  · rw [hPzeq]; linarith

theorem RhoTailRankin :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      ((Work.FIChain.DpiC x : ℝ)) ^ (-(Real.log 2 / Real.log ((Work.FIChain.Pzc x : ℕ) : ℝ)))
        ≤ (Real.log (x : ℝ)) ^ (-(262150 : ℤ)) := by
  refine ⟨10 ^ 50, ?_⟩
  intro x hx
  have hxR : (10 : ℝ) ^ 50 ≤ (x : ℝ) := by exact_mod_cast hx
  set L : ℝ := Real.log (x : ℝ) with hL
  set t : ℝ := Real.log L with ht
  have ht_eq : t = Real.log (Real.log (x : ℝ)) := by rw [ht, hL]
  have hL100 : 100 ≤ L := by
    have h1 : Real.log ((10 : ℝ) ^ 50) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by positivity) hxR
    have h2 : Real.log ((10 : ℝ) ^ 50) = 50 * Real.log 10 := by
      rw [Real.log_pow]; norm_num
    have hlog10 : (2 : ℝ) ≤ Real.log 10 := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 10)).mpr ?_
      have h2e : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    rw [hL]; linarith
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have ht4 : 4 ≤ t := by
    have hlog100 : (4 : ℝ) ≤ Real.log 100 := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 100)).mpr ?_
      have h2 : Real.exp (2 : ℝ) ≤ 10 := by
        have h2e : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
      have h4 : Real.exp (4 : ℝ) = Real.exp 2 ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h4]; nlinarith [h2, Real.exp_pos 2]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 100) hL100
    rw [ht]; linarith
  have htpos : 0 < t := by linarith
  have ht2 : (16 : ℝ) ≤ t ^ 2 := by nlinarith
  -- `Pcut` facts in terms of `t`
  have hPzeq : Pzc x = Work.FITop.Pcut x := rfl
  have hPzlo : t ^ 2 ≤ Real.log (Pzc x : ℝ) := by
    have h := Work.FITop.FI_log_Pcut_ge x
    rw [← ht_eq] at h
    rw [hPzeq]; exact h
  have hPzhi : Real.log (Pzc x : ℝ) ≤ 2 * t ^ 2 := by
    have h := Work.FITop.FI_log_Pcut_le x
    rw [← ht_eq] at h
    have hlog2le : Real.log 2 ≤ t ^ 2 := by
      have h1 : Real.log 2 ≤ 1 := by
        have h' := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
        linarith
      linarith
    rw [hPzeq]; linarith
  have hlogPz_pos : 0 < Real.log (Pzc x : ℝ) := by linarith
  -- the `DpiC` lower bound
  have hDpi : Real.exp ((2 : ℝ) ^ 40 * t ^ 3) ≤ (DpiC x : ℝ) := by
    rw [ht_eq]
    rw [DpiC, Dpi]
    exact Nat.le_ceil _
  -- the Rankin exponent
  set σ : ℝ := Real.log 2 / Real.log (Pzc x : ℝ) with hσdef
  have hσ_pos : 0 < σ := by
    rw [hσdef]
    exact div_pos (Real.log_pos (by norm_num)) hlogPz_pos
  have hσ_ge : Real.log 2 / (2 * t ^ 2) ≤ σ := by
    rw [hσdef]
    exact div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
      hlogPz_pos hPzhi
  have hA : 0 ≤ (2 : ℝ) ^ 40 * t ^ 3 := by
    have h2 : (0 : ℝ) < t ^ 3 := by positivity
    exact mul_nonneg (by positivity) h2.le
  have hneg : -σ ≤ 0 := by linarith
  calc (DpiC x : ℝ) ^ (-σ)
      ≤ (Real.exp ((2 : ℝ) ^ 40 * t ^ 3)) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hDpi hneg
    _ = Real.exp (-σ * ((2 : ℝ) ^ 40 * t ^ 3)) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; ring_nf
    _ ≤ Real.exp (-(Real.log 2 / (2 * t ^ 2)) * ((2 : ℝ) ^ 40 * t ^ 3)) := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_right hσ_ge hA
        linarith
    _ = Real.exp (-((2 : ℝ) ^ 40 * Real.log 2 / 2) * t) := by
        congr 1
        have htne : t ≠ 0 := ne_of_gt htpos
        field_simp
    _ = L ^ (-((2 : ℝ) ^ 40 * Real.log 2 / 2)) := by
        rw [Real.rpow_def_of_pos hLpos, ht]; ring_nf
    _ ≤ L ^ (-(262150 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hL1
        linarith [RhoTailRankin_num]
    _ = L ^ (-(262150 : ℤ)) := by
        have h : ((-(262150 : ℤ) : ℤ) : ℝ) = -(262150 : ℝ) := by norm_num
        rw [← h]
        exact Real.rpow_intCast L (-(262150 : ℤ))

end

end Work.FIChain
