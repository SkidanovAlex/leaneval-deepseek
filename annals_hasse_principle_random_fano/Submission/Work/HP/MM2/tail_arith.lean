import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.six_le_NN

namespace Work.HP.MM2

/-- **The numeric core of the tail bound.**  For fixed `K, ι > 0` there are `C, B₀ > 0` so that,
uniformly in `A, B` with `B₀ ≤ B` and `B^{5/6} ≤ A ≤ B²`,
`2K W^N/A ≤ C·(8ι A^{N-2}/(αW)²)/log A`, where `W = bigW (wOf B)`, `α = log B`, `N = NN d n`.
Route (`N ≥ 6` by `six_le_NN`): multiply by `A(αW)²log A > 0`; the claim becomes
`2K W^{N+2}α²log A ≤ C·8ι·A^{N-1}`.  `bigW_le_pow ε hε` with `ε = (5/6)(N-1)/(2(N+2)) > 0`
gives `W ≤ B^ε` for `B ≥ B₀₁`, so `W^{N+2} ≤ B^δ` with `δ = (5/12)(N-1) = ε(N+2)`;
`A^{N-1} ≥ (B^{5/6})^{N-1} = B^{2δ}` since `A ≥ B^{5/6}` (use `Real.rpow_le_rpow` and
`Real.rpow_mul`/`Real.rpow_natCast`); `α² log A ≤ 2(log B)³` since `A ≤ B²`; and
`Real.log_le_rpow_div` gives `(log B)³ ≤ (3/δ)³B^δ` for `B > 0`.  Then
`C = 4K(3/δ)³/(8ι)` works, with `B₀` any bound `≥ max B₀₁ (Real.exp 2)` ensuring `A > 1`. -/
theorem tail_arith (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (K ι : ℝ) (hK : 0 < K) (hι : 0 < ι) :
    ∃ C B₀ : ℝ, 0 < C ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      2 * K * ((bigW (wOf B) : ℕ) : ℝ) ^ (NN d n) / A
        ≤ C * (8 * ι * A ^ (NN d n - 2) / ((Real.log B * ((bigW (wOf B) : ℕ) : ℝ)) ^ 2))
            / Real.log A := by
  set N : ℕ := NN d n with hNdef
  have hN6 : 6 ≤ N := by rw [hNdef]; exact six_le_NN d n hd hdn
  have hN1 : 1 ≤ N := by omega
  -- δ = (5/12)(N-1), the exponent saving available for `W`
  set δ : ℝ := (5 / 12) * ((N : ℝ) - 1) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  -- ε = δ/(N+2), the exponent in `bigW_le_pow`
  set ε : ℝ := δ / ((N : ℝ) + 2) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hN2pos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hεδ : ε * ((N : ℝ) + 2) = δ := by
    rw [hεdef]; exact div_mul_cancel₀ δ hN2pos.ne'
  have hδ2 : 2 * δ = (5 / 6) * ((N : ℝ) - 1) := by rw [hδdef]; ring
  obtain ⟨B₁, hB₁⟩ := bigW_le_pow ε hεpos
  set C : ℝ := 4 * K * (3 / δ) ^ 3 / (8 * ι) with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  refine ⟨C, max B₁ (Real.exp 2), hCpos, ?_⟩
  intro A B hB hA1 hA2
  set W : ℝ := ((bigW (wOf B) : ℕ) : ℝ) with hWdef
  have hWge1 : 1 ≤ W := by rw [hWdef]; exact_mod_cast one_le_bigW (wOf B)
  have hWpos : 0 < W := lt_of_lt_of_le one_pos hWge1
  have hBge : Real.exp 2 ≤ B := le_trans (le_max_right _ _) hB
  have hB₁le : B₁ ≤ B := le_trans (le_max_left _ _) hB
  have hWle : W ≤ B ^ ε := by rw [hWdef]; exact hB₁ B hB₁le
  have hB1 : 1 < B := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hBge
  have hBpos : 0 < B := lt_trans one_pos hB1
  have hlogBpos : 0 < Real.log B := Real.log_pos hB1
  have hAgt1 : 1 < A := lt_of_lt_of_le (Real.one_lt_rpow hB1 (by norm_num : (0:ℝ) < 5/6)) hA1
  have hApos : 0 < A := lt_trans one_pos hAgt1
  have hlogApos : 0 < Real.log A := Real.log_pos hAgt1
  -- `log A ≤ 2 log B` because `A ≤ B²`
  have hlogA_le : Real.log A ≤ 2 * Real.log B := by
    have h := Real.log_le_log hApos hA2
    rw [Real.log_pow] at h
    simpa using h
  -- `W^{N+2} ≤ B^δ`
  have hWpow : W ^ (N + 2) ≤ B ^ δ := by
    have h1 : W ^ (N + 2) ≤ (B ^ ε) ^ (N + 2) :=
      pow_le_pow_left₀ (le_trans zero_le_one hWge1) hWle (N + 2)
    refine h1.trans (le_of_eq ?_)
    rw [← Real.rpow_natCast (B ^ ε) (N + 2), ← Real.rpow_mul hBpos.le]
    congr 1
    push_cast
    exact hεδ
  -- `B^{2δ} ≤ A^{N-1}` because `A ≥ B^{5/6}`
  have hB2δ_le : B ^ (2 * δ) ≤ A ^ (N - 1) := by
    have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by simpa using Nat.cast_sub hN1
    have h_eq : B ^ (2 * δ) = (B ^ ((5 : ℝ) / 6)) ^ (N - 1) := by
      rw [← Real.rpow_natCast (B ^ ((5 : ℝ) / 6)) (N - 1), ← Real.rpow_mul hBpos.le]
      congr 1
      rw [hc]
      exact hδ2
    rw [h_eq]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hBpos.le _) hA1 (N - 1)
  -- `(log B)³ ≤ (3/δ)³ B^δ`
  have hlog3 : (Real.log B) ^ 3 ≤ (3 / δ) ^ 3 * B ^ δ := by
    have hδ3pos : 0 < δ / 3 := by positivity
    have h := Real.log_le_rpow_div hBpos.le hδ3pos
    have hdiv : B ^ (δ / 3) / (δ / 3) = (3 / δ) * B ^ (δ / 3) := by
      field_simp
    rw [hdiv] at h
    have hcube : (Real.log B) ^ 3 ≤ ((3 / δ) * B ^ (δ / 3)) ^ 3 :=
      pow_le_pow_left₀ (le_of_lt hlogBpos) h 3
    have heq2 : ((3 / δ) * B ^ (δ / 3)) ^ 3 = (3 / δ) ^ 3 * B ^ δ := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast (B ^ (δ / 3)) 3, ← Real.rpow_mul hBpos.le]
      congr 1
      push_cast
      ring
    linarith [hcube, heq2]
  -- the cleared inequality `2K W^{N+2} α² log A ≤ 4K(3/δ)³ A^{N-1}`
  have hKEY : 2 * K * (Real.log B) ^ 2 * W ^ (N + 2) * Real.log A
      ≤ 4 * K * (3 / δ) ^ 3 * A ^ (N - 1) := by
    have h1 : 2 * K * (Real.log B) ^ 2 * W ^ (N + 2) * Real.log A
        ≤ 2 * K * (Real.log B) ^ 2 * B ^ δ * Real.log A := by
      have hnn : 0 ≤ 2 * K * (Real.log B) ^ 2 * Real.log A := by positivity
      have hh := mul_le_mul_of_nonneg_left hWpow hnn
      convert hh using 1 <;> ring
    have h2 : 2 * K * (Real.log B) ^ 2 * B ^ δ * Real.log A
        ≤ 2 * K * (Real.log B) ^ 2 * B ^ δ * (2 * Real.log B) := by
      have hnn : 0 ≤ 2 * K * (Real.log B) ^ 2 * B ^ δ := by positivity
      exact mul_le_mul_of_nonneg_left hlogA_le hnn
    have h3 : 2 * K * (Real.log B) ^ 2 * B ^ δ * (2 * Real.log B)
        = 4 * K * (Real.log B) ^ 3 * B ^ δ := by ring
    have h4 : 4 * K * (Real.log B) ^ 3 * B ^ δ
        ≤ 4 * K * ((3 / δ) ^ 3 * B ^ δ) * B ^ δ := by
      have hnn : 0 ≤ 4 * K * B ^ δ := by positivity
      have hh := mul_le_mul_of_nonneg_left hlog3 hnn
      convert hh using 1 <;> ring
    have h5 : 4 * K * ((3 / δ) ^ 3 * B ^ δ) * B ^ δ = 4 * K * (3 / δ) ^ 3 * B ^ (2 * δ) := by
      have hBdBd : B ^ δ * B ^ δ = B ^ (2 * δ) := by
        rw [← Real.rpow_add hBpos]
        congr 1
        ring
      calc 4 * K * ((3 / δ) ^ 3 * B ^ δ) * B ^ δ
          = 4 * K * (3 / δ) ^ 3 * (B ^ δ * B ^ δ) := by ring
        _ = 4 * K * (3 / δ) ^ 3 * B ^ (2 * δ) := by rw [hBdBd]
    have h6 : 4 * K * (3 / δ) ^ 3 * B ^ (2 * δ) ≤ 4 * K * (3 / δ) ^ 3 * A ^ (N - 1) := by
      exact mul_le_mul_of_nonneg_left hB2δ_le (by positivity)
    calc 2 * K * (Real.log B) ^ 2 * W ^ (N + 2) * Real.log A
        ≤ 2 * K * (Real.log B) ^ 2 * B ^ δ * Real.log A := h1
      _ ≤ 2 * K * (Real.log B) ^ 2 * B ^ δ * (2 * Real.log B) := h2
      _ = 4 * K * (Real.log B) ^ 3 * B ^ δ := h3
      _ ≤ 4 * K * ((3 / δ) ^ 3 * B ^ δ) * B ^ δ := h4
      _ = 4 * K * (3 / δ) ^ 3 * B ^ (2 * δ) := h5
      _ ≤ 4 * K * (3 / δ) ^ 3 * A ^ (N - 1) := h6
  have hCmul : C * 8 * ι = 4 * K * (3 / δ) ^ 3 := by
    rw [hCdef]
    field_simp
  have e3 : C * 8 * ι * A ^ (N - 2) * A = 4 * K * (3 / δ) ^ 3 * A ^ (N - 1) := by
    have hN2 : N - 2 + 1 = N - 1 := by omega
    calc C * 8 * ι * A ^ (N - 2) * A = (C * 8 * ι) * (A ^ (N - 2) * A) := by ring
      _ = (C * 8 * ι) * A ^ (N - 2 + 1) := by rw [pow_succ]
      _ = (C * 8 * ι) * A ^ (N - 1) := by rw [hN2]
      _ = 4 * K * (3 / δ) ^ 3 * A ^ (N - 1) := by rw [hCmul]
  have e1 : 2 * K * W ^ N * ((Real.log B * W) ^ 2 * Real.log A)
      = 2 * K * (Real.log B) ^ 2 * (W ^ N * W ^ 2) * Real.log A := by
    rw [mul_pow]; ring
  have e1' : 2 * K * (Real.log B) ^ 2 * (W ^ N * W ^ 2) * Real.log A
      = 2 * K * (Real.log B) ^ 2 * W ^ (N + 2) * Real.log A := by
    rw [pow_add]
  -- clear the denominators of the goal
  have hDpos : 0 < (Real.log B * W) ^ 2 * Real.log A := by positivity
  have hstep : 2 * K * W ^ N / A
      ≤ C * 8 * ι * A ^ (N - 2) / ((Real.log B * W) ^ 2 * Real.log A) := by
    rw [le_div_iff₀ hDpos]
    rw [div_mul_eq_mul_div, div_le_iff₀ hApos]
    rw [e1, e1', e3]
    exact hKEY
  have hrhs : C * (8 * ι * A ^ (N - 2) / (Real.log B * W) ^ 2) / Real.log A
      = C * 8 * ι * A ^ (N - 2) / ((Real.log B * W) ^ 2 * Real.log A) := by
    rw [← mul_div_assoc, div_div]
    ring
  calc 2 * K * W ^ N / A
      ≤ C * 8 * ι * A ^ (N - 2) / ((Real.log B * W) ^ 2 * Real.log A) := hstep
    _ = C * (8 * ι * A ^ (N - 2) / (Real.log B * W) ^ 2) / Real.log A := hrhs.symm

end Work.HP.MM2
