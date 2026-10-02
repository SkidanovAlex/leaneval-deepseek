import Submission.Work.ConeSwitch.MathlibNoHG

/-!
# Tools for the asymptotic thresholds of `cor:sparse_egj`

This module provides the elementary real-analysis lemmas used to build the
threshold `n₀` of `Work.Deep.Nibble.exists_threshold` (the asymptotic side
conditions of `cor:sparse_egj` in Kang--Kelly--Kühn--Methuku--Osthus, Annals 2023).

The workhorse is `mul_log_le_rpow`: for `a > 0` and `x ≥ 1`, `a * log x ≤ x ^ a`.
It is proved from `Real.log_le_sub_one_of_pos` and the identity
`Real.log (x ^ a) = a * log x`; it is the only analytic input of the whole
threshold computation (every "for large `n`" clause is reduced to a comparison
of powers of `n` and `D`).
-/

set_option autoImplicit false

namespace Work.Deep.Nibble

/-- **The basic log bound.**  For `a > 0` and `x ≥ 1`, `a * log x ≤ x ^ a`. -/
theorem mul_log_le_rpow {a x : ℝ} (_ha : 0 < a) (hx : 1 ≤ x) : a * Real.log x ≤ x ^ a := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h1 : Real.log (x ^ a) ≤ x ^ a - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 a)
  have h2 : x ^ a - 1 ≤ x ^ a := sub_le_self _ (by norm_num)
  calc a * Real.log x = Real.log (x ^ a) := (Real.log_rpow hx0 a).symm
    _ ≤ x ^ a - 1 := h1
    _ ≤ x ^ a := h2

/-- **Log bound, division form.**  For `a > 0` and `x ≥ 1`, `log x ≤ (2 / a) * x ^ (a / 2)`. -/
theorem log_le_two_div {a x : ℝ} (ha : 0 < a) (hx : 1 ≤ x) :
    Real.log x ≤ (2 / a) * x ^ (a / 2) := by
  have h := mul_log_le_rpow (by positivity : 0 < a / 2) hx
  have h2 : (2 / a) * (a / 2 * Real.log x) ≤ (2 / a) * x ^ (a / 2) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have h3 : (2 / a) * (a / 2 * Real.log x) = Real.log x := by
    field_simp
  calc Real.log x = (2 / a) * (a / 2 * Real.log x) := h3.symm
    _ ≤ (2 / a) * x ^ (a / 2) := h2

/-- **Squared log bound.**  For `a > 0` and `x ≥ 1`, `2 * (log x) ^ 2 ≤ (32 / a ^ 2) * x ^ (a / 2)`. -/
theorem two_log_sq_le {a x : ℝ} (ha : 0 < a) (hx : 1 ≤ x) :
    2 * (Real.log x) ^ 2 ≤ (32 / a ^ 2) * x ^ (a / 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h1 : Real.log x ≤ (4 / a) * x ^ (a / 4) := by
    have h := mul_log_le_rpow (by positivity : 0 < a / 4) hx
    have h2 : (4 / a) * (a / 4 * Real.log x) ≤ (4 / a) * x ^ (a / 4) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h3 : (4 / a) * (a / 4 * Real.log x) = Real.log x := by field_simp
    calc Real.log x = (4 / a) * (a / 4 * Real.log x) := h3.symm
      _ ≤ (4 / a) * x ^ (a / 4) := h2
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have key : (Real.log x) * (Real.log x) ≤ ((4 / a) * x ^ (a / 4)) * ((4 / a) * x ^ (a / 4)) :=
    mul_le_mul h1 h1 hlog0 (by positivity)
  have key2 : (Real.log x) ^ 2 ≤ ((4 / a) * x ^ (a / 4)) ^ 2 := by
    simpa [sq] using key
  have hsq : ((4 / a) * x ^ (a / 4)) ^ 2 = (16 / a ^ 2) * x ^ (a / 2) := by
    rw [mul_pow]
    have hL : (4 / a) ^ 2 = 16 / a ^ 2 := by field_simp; ring
    have hR : (x ^ (a / 4)) ^ 2 = x ^ (a / 2) := by
      rw [sq, ← Real.rpow_add hx0]
      congr 1
      ring
    rw [hL, hR]
  calc 2 * (Real.log x) ^ 2 ≤ 2 * ((16 / a ^ 2) * x ^ (a / 2)) :=
        mul_le_mul_of_nonneg_left (hsq ▸ key2) (by norm_num)
    _ = (32 / a ^ 2) * x ^ (a / 2) := by ring

/-- **Clauses 1 and 2 of `cor:sparse_egj`'s side conditions.**  For `κ > 0` there is `N` such
that for all `n ≥ N` and all `D ≥ n^{1/100}` one has `1 ≤ D` and `Δ₀ ≤ (1 + κ) * D`. -/
theorem sparse_egj_conds_1_2 {κ Δ₀ : ℝ} (hκ : 0 < κ) :
    ∃ N : ℝ, 0 < N ∧ ∀ n : ℕ, N ≤ (n : ℝ) → ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
      1 ≤ D ∧ Δ₀ ≤ (1 + κ) * D := by
  have hbase : 0 < max 1 Δ₀ := lt_of_lt_of_le (by norm_num) (le_max_left 1 Δ₀)
  refine ⟨(max 1 Δ₀) ^ ((100 : ℝ)), Real.rpow_pos_of_pos hbase _, ?_⟩
  intro n hn D hD
  have hN1 : (1 : ℝ) ≤ (max 1 Δ₀) ^ ((100 : ℝ)) := by
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) (le_max_left 1 Δ₀)
      (by norm_num : (0:ℝ) ≤ 100)
    rwa [Real.one_rpow] at h
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := hN1.trans hn
  have hD1 : 1 ≤ D := by
    have h1 : (1:ℝ) ≤ (n:ℝ) ^ ((1:ℝ)/100) := by
      have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hn1
        (by norm_num : (0:ℝ) ≤ (1:ℝ)/100)
      rwa [Real.one_rpow] at h
    exact h1.trans hD
  refine ⟨hD1, ?_⟩
  have hmax : max 1 Δ₀ ≤ (n:ℝ) ^ ((1:ℝ)/100) := by
    have h := Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hbase _)) hn
      (by norm_num : (0:ℝ) ≤ (1:ℝ)/100)
    have h2 : ((max 1 Δ₀) ^ ((100:ℝ)))^((1:ℝ)/100) = max 1 Δ₀ := by
      rw [← Real.rpow_mul (le_of_lt hbase) (100:ℝ) ((1:ℝ)/100),
        show (100:ℝ) * ((1:ℝ)/100) = 1 by norm_num, Real.rpow_one]
    rwa [h2] at h
  calc Δ₀ ≤ max 1 Δ₀ := le_max_right 1 Δ₀
    _ ≤ (n:ℝ) ^ ((1:ℝ)/100) := hmax
    _ ≤ D := hD
    _ ≤ (1 + κ) * D :=
        le_mul_of_one_le_left (le_of_lt (lt_of_lt_of_le zero_lt_one hD1)) (by linarith)

end Work.Deep.Nibble
