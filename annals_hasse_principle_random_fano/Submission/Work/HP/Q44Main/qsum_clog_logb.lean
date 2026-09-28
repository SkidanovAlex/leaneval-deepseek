import Mathlib

/-!
# `qsum_clog_logb`

For every `K ≥ 1` there is a constant `C > 0` with

`⌈logb 2 (8 K (Δ+1))⌉₊ + 1 ≤ C · log (2 Δ)`   for all real `Δ ≥ 1`.

This is the elementary "logarithmic growth" input: the number of dyadic windows below
`8 K (Δ+1)` grows at most like `log Δ`.

Writing `y = 8 K (Δ+1)` and `n = ⌈logb 2 y⌉₊`, we have (since `y ≥ 1`, so `logb 2 y ≥ 0`)

`n + 1 ≤ logb 2 y + 2 = log y / log 2 + 2`,

and `log y = log (8K) + log (Δ+1) ≤ log (8K) + log (2Δ)`, using `Δ + 1 ≤ 2Δ` for `Δ ≥ 1`.
Hence `n + 1 ≤ log (2Δ)/log 2 + M` with `M = log (8K)/log 2 + 2 ≥ 0`. Finally, since
`log (2Δ) ≥ log 2 > 0`, we have `1 ≤ log (2Δ)/log 2`, so `M ≤ M · log (2Δ)/log 2` and
therefore

`log (2Δ)/log 2 + M ≤ (1 + M)/log 2 · log (2Δ)`.

Thus `C = (1 + M)/log 2` works.
-/

namespace Work.HP.Q44Main

theorem qsum_clog_logb (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 1 ≤ Δ →
      (((⌈Real.logb 2 (8 * K * (Δ + 1))⌉₊ : ℕ) : ℝ) + 1) ≤ C * Real.log (2 * Δ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hlog8K : 0 ≤ Real.log (8 * K) := Real.log_nonneg (by nlinarith)
  set M : ℝ := Real.log (8 * K) / Real.log 2 + 2 with hM
  have hMpos : 0 < M := by
    have h1 : 0 ≤ Real.log (8 * K) / Real.log 2 := div_nonneg hlog8K hlog2.le
    rw [hM]; linarith
  refine ⟨(1 + M) / Real.log 2, ?_, ?_⟩
  · positivity
  · intro Δ hΔ
    set y : ℝ := 8 * K * (Δ + 1) with hy
    have hy1 : 1 ≤ y := by rw [hy]; nlinarith
    have hlogb_nonneg : 0 ≤ Real.logb 2 y := Real.logb_nonneg (by norm_num) hy1
    -- the ceiling is at most the logarithm plus one, and the logarithm is nonnegative
    have hceil_lt : ((⌈Real.logb 2 y⌉₊ : ℕ) : ℝ) + 1 ≤ Real.logb 2 y + 2 := by
      have h := Nat.ceil_lt_add_one (a := Real.logb 2 y) hlogb_nonneg
      linarith
    have hlogy : Real.log y = Real.log (8 * K) + Real.log (Δ + 1) := by
      rw [hy, Real.log_mul (by positivity) (by linarith)]
    have hDle : Real.log (Δ + 1) ≤ Real.log (2 * Δ) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlogb_le : Real.logb 2 y ≤ Real.log (2 * Δ) / Real.log 2 + Real.log (8 * K) / Real.log 2 := by
      have hlogb_eq : Real.logb 2 y = Real.log y / Real.log 2 := rfl
      rw [hlogb_eq, hlogy]
      have hthis : (Real.log (8 * K) + Real.log (Δ + 1)) / Real.log 2
          ≤ (Real.log (2 * Δ) + Real.log (8 * K)) / Real.log 2 :=
        div_le_div_of_nonneg_right (by linarith) hlog2.le
      calc (Real.log (8 * K) + Real.log (Δ + 1)) / Real.log 2
          ≤ (Real.log (2 * Δ) + Real.log (8 * K)) / Real.log 2 := hthis
        _ = Real.log (2 * Δ) / Real.log 2 + Real.log (8 * K) / Real.log 2 := by ring
    have hmain : ((⌈Real.logb 2 (8 * K * (Δ + 1))⌉₊ : ℕ) : ℝ) + 1
        ≤ Real.log (2 * Δ) / Real.log 2 + M := by
      have hceileq : ⌈Real.logb 2 (8 * K * (Δ + 1))⌉₊ = ⌈Real.logb 2 y⌉₊ := by rw [hy]
      rw [hceileq, hM]
      linarith
    -- absorb the additive constant into the positive factor `log (2Δ)/log 2 ≥ 1`
    have hLle : Real.log 2 ≤ Real.log (2 * Δ) := Real.log_le_log (by norm_num) (by linarith)
    have hr : 1 ≤ Real.log (2 * Δ) / Real.log 2 := by
      rw [le_div_iff₀ hlog2]; linarith
    have hfin : Real.log (2 * Δ) / Real.log 2 + M ≤ ((1 + M) / Real.log 2) * Real.log (2 * Δ) := by
      have h1 : M ≤ M * (Real.log (2 * Δ) / Real.log 2) := by
        have := mul_le_mul_of_nonneg_left hr hMpos.le
        simpa using this
      have h2 : ((1 + M) / Real.log 2) * Real.log (2 * Δ)
          = (1 + M) * (Real.log (2 * Δ) / Real.log 2) := by ring
      rw [h2]; nlinarith
    exact le_trans hmain hfin

end Work.HP.Q44Main
