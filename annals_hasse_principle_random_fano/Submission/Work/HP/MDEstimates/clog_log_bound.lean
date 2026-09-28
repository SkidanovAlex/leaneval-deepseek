import Mathlib

namespace Work.HP.MDEstimates

/-- Upper bound for `Nat.clog 2 n` in terms of the real logarithm:
the binary logarithm of a natural number is at most `log n / log 2 + 1`. -/
lemma clog_two_le_log_ratio (n : ℕ) :
    (Nat.clog 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hn : n ≤ 1
  · rw [Nat.clog_of_right_le_one hn 2]
    interval_cases n <;> simp
  · have hn' : 1 < n := by omega
    have hk : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) hn'
    have hp : 2 ^ (Nat.clog 2 n).pred < n := Nat.pow_pred_clog_lt_self (by norm_num) hn'
    have hlog : Real.log ((2:ℝ) ^ (Nat.clog 2 n).pred) ≤ Real.log (n:ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hp.le)
    rw [Real.log_pow] at hlog
    have hcast : (((Nat.clog 2 n).pred : ℕ) : ℝ) = (Nat.clog 2 n : ℝ) - 1 := by
      rw [Nat.pred_eq_sub_one, Nat.cast_pred hk]
    rw [hcast] at hlog
    have h2 : (Nat.clog 2 n : ℝ) - 1 ≤ Real.log (n:ℝ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]; linarith
    linarith

theorem clog_log_bound (Kmk : ℝ) (hKmk : 1 ≤ Kmk) :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 1 ≤ Δ →
      ((Nat.clog 2 ⌈8 * Kmk * (Δ + 1)⌉₊ : ℕ) : ℝ) + 1 ≤ C * Real.log (2 * Δ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog16 : 0 ≤ Real.log (16 * Kmk) := Real.log_nonneg (by nlinarith)
  set M : ℝ := Real.log (16 * Kmk) / Real.log 2 + 2 with hM
  have hMpos : 0 < M := by
    have h1 : 0 ≤ Real.log (16 * Kmk) / Real.log 2 := div_nonneg hlog16 (le_of_lt hlog2)
    rw [hM]; linarith
  refine ⟨(1 + M) / Real.log 2, ?_, ?_⟩
  · positivity
  · intro Δ hΔ
    set y : ℝ := 8 * Kmk * (Δ + 1) with hy
    set n : ℕ := ⌈y⌉₊ with hn
    have hypos : 0 < y := by rw [hy]; nlinarith [hKmk, hΔ]
    have hnRpos : 0 < (n:ℝ) := lt_of_lt_of_le hypos (by rw [hn]; exact Nat.le_ceil y)
    have hnlt : (n:ℝ) < y + 1 := by rw [hn]; exact Nat.ceil_lt_add_one (le_of_lt hypos)
    have hyle : y + 1 ≤ 16 * Kmk * (Δ + 1) := by rw [hy]; nlinarith [hKmk, hΔ]
    have hnle : (n:ℝ) ≤ 16 * Kmk * (Δ + 1) := le_of_lt (lt_of_lt_of_le hnlt hyle)
    have hlogn : Real.log (n:ℝ) ≤ Real.log (16 * Kmk * (Δ + 1)) :=
      Real.log_le_log hnRpos hnle
    have h16ne : (16:ℝ) * Kmk ≠ 0 := by positivity
    have hDne : (Δ + 1) ≠ 0 := by linarith
    have hlogmul : Real.log (16 * Kmk * (Δ + 1)) = Real.log (16*Kmk) + Real.log (Δ+1) :=
      Real.log_mul h16ne hDne
    have hDle : Real.log (Δ + 1) ≤ Real.log (2 * Δ) :=
      Real.log_le_log (by linarith) (by linarith)
    have hkey : Real.log (n:ℝ) ≤ Real.log (16*Kmk) + Real.log (2*Δ) := by
      rw [hlogmul] at hlogn; linarith
    have hclog := clog_two_le_log_ratio n
    have hmain : ((Nat.clog 2 n : ℕ) : ℝ) + 1 ≤ Real.log (2*Δ)/Real.log 2 + M := by
      have hsplit : Real.log (n:ℝ)/Real.log 2 ≤ (Real.log (16*Kmk) + Real.log (2*Δ))/Real.log 2 :=
        div_le_div_of_nonneg_right hkey (le_of_lt hlog2)
      have hring : (Real.log (16*Kmk) + Real.log (2*Δ))/Real.log 2
          = Real.log (2*Δ)/Real.log 2 + Real.log (16*Kmk)/Real.log 2 := by ring
      rw [hring] at hsplit
      rw [hM]
      linarith
    have hLle : Real.log 2 ≤ Real.log (2 * Δ) := Real.log_le_log (by norm_num) (by linarith)
    have hr : 1 ≤ Real.log (2*Δ)/Real.log 2 := by
      rw [le_div_iff₀ hlog2]; linarith
    have hfin : Real.log (2*Δ)/Real.log 2 + M ≤ ((1+M)/Real.log 2) * Real.log (2*Δ) := by
      have h1 : M ≤ M * (Real.log (2*Δ)/Real.log 2) := by
        have := mul_le_mul_of_nonneg_left hr (le_of_lt hMpos)
        simpa using this
      have h2 : ((1+M)/Real.log 2) * Real.log (2*Δ) = (1+M) * (Real.log (2*Δ)/Real.log 2) := by ring
      rw [h2]; nlinarith
    linarith

end Work.HP.MDEstimates
