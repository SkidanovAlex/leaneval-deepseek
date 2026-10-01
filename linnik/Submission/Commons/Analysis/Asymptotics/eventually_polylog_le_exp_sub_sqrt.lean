import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

namespace Commons.Analysis.Asymptotics

/-- Auxiliary domination fact: for `C > 0`, a fixed power `t^k` of `t` is eventually
bounded by `exp (t - c * sqrt t)`. -/
private lemma key_exp_dom (c : ℝ) (hc : 0 < c) (k : ℕ) (C : ℝ) (hC : 0 < C) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      C * t ^ k ≤ Real.exp (t - c * Real.sqrt t) := by
  let S : ℝ := max 1 (2 * (k : ℝ) + c + |Real.log C| + 2)
  have hS1 : 1 ≤ S := le_max_left _ _
  have hS2 : 2 * (k : ℝ) + c + |Real.log C| + 2 ≤ S := le_max_right _ _
  have hSpos : 0 < S := lt_of_lt_of_le one_pos hS1
  have hsqpos : 0 < S ^ 2 := by positivity
  refine ⟨S ^ 2, le_of_lt hsqpos, ?_⟩
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le hsqpos ht
  set s : ℝ := Real.sqrt t with hs_def
  have hs_ge_S : S ≤ s := by
    have h1 : Real.sqrt (S ^ 2) ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
    rw [Real.sqrt_sq (le_of_lt hSpos)] at h1
    rw [← hs_def] at h1
    exact h1
  have hs1 : 1 ≤ s := le_trans hS1 hs_ge_S
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs1
  have hs2 : s ^ 2 = t := by
    rw [hs_def]
    exact Real.sq_sqrt (le_of_lt htpos)
  have hlogC_le : Real.log C ≤ s := by
    have habs : |Real.log C| ≤ S := by
      have : |Real.log C| ≤ 2 * (k : ℝ) + c + |Real.log C| + 2 := by
        have hk0 : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
        linarith
      linarith
    linarith [le_abs_self (Real.log C), habs, hs_ge_S]
  have hlogs_le : Real.log s ≤ s := by
    have := Real.log_le_sub_one_of_pos hspos
    linarith
  have hsc_ge : 2 * (k : ℝ) + c + 1 ≤ s := by
    have h1 : 2 * (k : ℝ) + c + 1 ≤ S := by
      have habs0 : (0 : ℝ) ≤ |Real.log C| := abs_nonneg _
      linarith
    linarith
  have hlogt : Real.log t = 2 * Real.log s := by
    rw [← hs2, Real.log_pow]
    ring
  have hbound : Real.log (C * t ^ k) ≤ t - c * Real.sqrt t := by
    rw [Real.log_mul (ne_of_gt hC) (pow_ne_zero k (ne_of_gt htpos)), Real.log_pow, hlogt]
    rw [← hs_def, ← hs2]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : (k : ℝ) * (2 * Real.log s) ≤ (k : ℝ) * (2 * s) := by
      apply mul_le_mul_of_nonneg_left _ hk0
      linarith
    have h2 : Real.log C + (k : ℝ) * (2 * Real.log s) ≤ (2 * (k : ℝ) + 1) * s := by
      nlinarith [hlogC_le, h1]
    have h3 : (2 * (k : ℝ) + c + 1) * s ≤ s ^ 2 := by
      nlinarith [hsc_ge, hspos]
    nlinarith [h2, h3]
  calc C * t ^ k = Real.exp (Real.log (C * t ^ k)) := (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp (t - c * Real.sqrt t) := Real.exp_le_exp.mpr hbound

theorem eventually_polylog_le_exp_sub_sqrt (c : ℝ) (hc : 0 < c) (k : ℕ) (C : ℝ)
    (hC : 0 ≤ C) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      C * (Real.log x) ^ k ≤ Real.exp (Real.log x - c * Real.sqrt (Real.log x)) := by
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · refine ⟨0, fun x _ => ?_⟩
    rw [← hC0, zero_mul]
    exact Real.exp_nonneg _
  · obtain ⟨T, hT0, hT⟩ := key_exp_dom c hc k C hCpos
    refine ⟨Real.exp T, fun x hx => ?_⟩
    have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos T) hx
    have hlogx : T ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos T) hx
      rwa [Real.log_exp] at h
    exact hT (Real.log x) hlogx

end Commons.Analysis.Asymptotics