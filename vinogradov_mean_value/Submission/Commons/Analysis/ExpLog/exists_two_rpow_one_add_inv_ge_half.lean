import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Commons.Analysis.ExpLog.log_ratio_sub

namespace Commons.Analysis.ExpLog

theorem exists_two_rpow_one_add_inv_ge_half (l m : ℕ) (hl : 1 ≤ l) (hm : 4 ≤ m) :
    ∃ B : ℕ, (B : ℝ) ≤ 2 + 2 * (l : ℝ) * (Real.log (Real.log (m : ℝ) + 2) + 1) ∧
      (m : ℝ) / 2 ≤ (2 : ℝ) ^ ((1 + 1 / (l : ℝ)) ^ B) := by
  have hlR : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
  have hmR : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hMpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogMpos : (0 : ℝ) < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hlogM2pos : (0 : ℝ) < Real.log ((m : ℝ) / 2) := by
    apply Real.log_pos; linarith
  set r : ℝ := 1 + 1 / (l : ℝ) with hrdef
  set A : ℝ := 2 + 2 * (l : ℝ) * (Real.log (Real.log (m : ℝ) + 2) + 1) with hAdef
  set T : ℝ := Real.log ((m : ℝ) / 2) / Real.log 2 with hTdef
  have hr1 : 1 ≤ r := by
    rw [hrdef]
    have hpos : (0 : ℝ) < 1 / (l : ℝ) := by positivity
    linarith
  have hrpos : 0 < r := by linarith
  have hlogr : 1 / (2 * (l : ℝ)) ≤ Real.log r := by
    have hlog_ratio := log_ratio_sub ((l : ℝ) + 1) (l : ℝ) hlpos (by linarith)
    have hEq : (((l : ℝ) + 1) - (l : ℝ)) / ((l : ℝ) + 1) = 1 / ((l : ℝ) + 1) := by ring
    rw [hEq] at hlog_ratio
    have hratio : ((l : ℝ) + 1) / (l : ℝ) = r := by
      rw [hrdef]; field_simp
    rw [hratio] at hlog_ratio
    have hle : 1 / (2 * (l : ℝ)) ≤ 1 / ((l : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by linarith : (0 : ℝ) < (l : ℝ) + 1)
      linarith
    linarith
  have hA_lower : Real.log (Real.log (m : ℝ) + 2) + 1 ≤ (A - 1) * Real.log r := by
    have hA1 : A - 1 = 1 + 2 * (l : ℝ) * (Real.log (Real.log (m : ℝ) + 2) + 1) := by
      rw [hAdef]; ring
    rw [hA1]
    have hloglog_pos : 0 < Real.log (Real.log (m : ℝ) + 2) := by
      apply Real.log_pos; linarith
    have hfac : 0 ≤ 1 + 2 * (l : ℝ) * (Real.log (Real.log (m : ℝ) + 2) + 1) := by positivity
    have hmul : (1 + 2 * (l : ℝ) * (Real.log (Real.log (m : ℝ) + 2) + 1)) * (1 / (2 * (l : ℝ)))
        = 1 / (2 * (l : ℝ)) + (Real.log (Real.log (m : ℝ) + 2) + 1) := by
      field_simp
    have h1 : 1 / (2 * (l : ℝ)) + (Real.log (Real.log (m : ℝ) + 2) + 1)
        ≤ (1 + 2 * (l : ℝ) * (Real.log (Real.log (m : ℝ) + 2) + 1)) * Real.log r := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_left hlogr hfac
    have hnn : (0 : ℝ) ≤ 1 / (2 * (l : ℝ)) := by positivity
    linarith
  have hTpos : 0 < T := by
    rw [hTdef]
    exact div_pos hlogM2pos hlog2pos
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    rw [le_div_iff₀ hlog2pos]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ (m : ℝ) / 2)
    linarith
  have hT_le : Real.log T ≤ Real.log (Real.log (m : ℝ) + 2) + 1 := by
    have hTle : T ≤ Real.log (m : ℝ) / Real.log 2 := by
      rw [hTdef]
      apply div_le_div_of_nonneg_right _ (le_of_lt hlog2pos)
      exact Real.log_le_log (by positivity) (by linarith)
    have hlogTle : Real.log T ≤ Real.log (Real.log (m : ℝ) / Real.log 2) :=
      Real.log_le_log (by linarith) hTle
    have hlogdiv : Real.log (Real.log (m : ℝ) / Real.log 2)
        = Real.log (Real.log (m : ℝ)) + (- Real.log (Real.log 2)) := by
      rw [Real.log_div (ne_of_gt hlogMpos) (ne_of_gt hlog2pos)]
      ring
    rw [hlogdiv] at hlogTle
    have hconst : - Real.log (Real.log 2) ≤ 1 := by
      have hpos : 0 < 1 / Real.log 2 := by positivity
      have hle : Real.log (1 / Real.log 2) ≤ 1 := by
        rw [Real.log_le_iff_le_exp hpos]
        rw [div_le_iff₀ hlog2pos]
        nlinarith [Real.exp_one_gt_two, Real.log_two_gt_d9]
      have hthis : Real.log (1 / Real.log 2) = - Real.log (Real.log 2) := by
        rw [one_div, Real.log_inv]
      linarith [hthis ▸ hle]
    have hlogM_le : Real.log (Real.log (m : ℝ)) ≤ Real.log (Real.log (m : ℝ) + 2) :=
      Real.log_le_log hlogMpos (by linarith)
    linarith
  have hlogT_bound : Real.log T ≤ (A - 1) * Real.log r := le_trans hT_le hA_lower
  have hT_rpow : T ≤ r ^ (A - 1) := by
    rw [Real.rpow_def_of_pos hrpos (A - 1), ← Real.exp_log hTpos]
    apply Real.exp_le_exp.mpr
    rw [mul_comm]
    exact hlogT_bound
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    have hloglog_pos : 0 < Real.log (Real.log (m : ℝ) + 2) := by
      apply Real.log_pos; linarith
    positivity
  have hfloor_ge : A - 1 ≤ ((Nat.floor A : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one A
    linarith
  have hT_pow : T ≤ r ^ Nat.floor A := by
    calc T ≤ r ^ (A - 1) := hT_rpow
      _ ≤ r ^ (((Nat.floor A : ℕ)) : ℝ) := Real.rpow_le_rpow_of_exponent_le hr1 hfloor_ge
      _ = r ^ Nat.floor A := Real.rpow_natCast r (Nat.floor A)
  have h2T : (2 : ℝ) ^ T = (m : ℝ) / 2 := by
    rw [hTdef, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hsimp : Real.log 2 * (Real.log ((m : ℝ) / 2) / Real.log 2) = Real.log ((m : ℝ) / 2) := by
      field_simp
    rw [hsimp, Real.exp_log (by positivity : (0 : ℝ) < (m : ℝ) / 2)]
  refine ⟨Nat.floor A, ?_, ?_⟩
  · have := Nat.floor_le hA0
    rw [hAdef] at this
    exact this
  · rw [← h2T]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hT_pow

end Commons.Analysis.ExpLog