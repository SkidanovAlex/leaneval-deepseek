import Mathlib

namespace Work.HP.MM2

/-- For `A ≥ 1` we have `√(log A) ≤ A^{1/4}`. -/
lemma sqrt_log_le_rpow_quarter {A : ℝ} (hA : 1 ≤ A) :
    Real.sqrt (Real.log A) ≤ A ^ ((1 : ℝ) / 4) := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hlog : 0 ≤ Real.log A := Real.log_nonneg hA
  have h1 : Real.sqrt (Real.log A) ≤ 1 + Real.log A / 4 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    nlinarith [sq_nonneg (Real.log A - 4)]
  have h2 : 1 + Real.log A / 4 ≤ Real.exp (Real.log A / 4) := by
    have := Real.add_one_le_exp (Real.log A / 4)
    linarith
  have h3 : Real.exp (Real.log A / 4) = A ^ ((1 : ℝ) / 4) := by
    rw [Real.rpow_def_of_pos hApos]
    congr 1
    ring
  linarith [h1, h2, h3.le]

theorem Sigma1mix_arith (k1 k2 C : ℝ) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      0 < A ∧ 0 < B ∧ 0 < Real.log A ∧
        k1 / A ^ ((1 : ℝ) / 4) + k2 / Real.log B ^ ((1 : ℝ) / 2) + C / Real.log A
          ≤ K / Real.log A ^ ((1 : ℝ) / 2) := by
  refine ⟨|k1| + 2 * |k2| + |C| + 1, Real.exp 2, ?_, ?_⟩
  · have h1 := abs_nonneg k1; have h2 := abs_nonneg k2; have h3 := abs_nonneg C
    linarith
  · intro A B hB hAB hABsq
    have hBpos : 0 < B := lt_of_lt_of_le (Real.exp_pos 2) hB
    have hlogB2 : 2 ≤ Real.log B := by
      have h : Real.log (Real.exp 2) ≤ Real.log B := Real.log_le_log (Real.exp_pos 2) hB
      rwa [Real.log_exp] at h
    have hlogBpos : 0 < Real.log B := by linarith
    have hB56pos : 0 < B ^ ((5 : ℝ) / 6) := Real.rpow_pos_of_pos hBpos _
    have hApos : 0 < A := lt_of_lt_of_le hB56pos hAB
    -- A ≥ exp(5/3) > 1
    have hA1 : 1 ≤ A := by
      have h1 : Real.exp ((5 : ℝ) / 3) ≤ A := by
        calc Real.exp ((5 : ℝ) / 3) ≤ Real.exp ((5 : ℝ) / 6 * Real.log B) := by
              apply Real.exp_le_exp.mpr
              nlinarith [hlogB2]
          _ = B ^ ((5 : ℝ) / 6) := by
              rw [Real.rpow_def_of_pos hBpos]; congr 1; ring
          _ ≤ A := hAB
      have h2 : (1 : ℝ) ≤ Real.exp ((5 : ℝ) / 3) := by
        have := Real.add_one_le_exp ((5 : ℝ) / 3); linarith
      linarith
    have hlogA53 : (5 : ℝ) / 3 ≤ Real.log A := by
      have h : Real.log (B ^ ((5 : ℝ) / 6)) ≤ Real.log A := Real.log_le_log hB56pos hAB
      rw [Real.log_rpow hBpos] at h
      nlinarith [h, hlogB2]
    have hlogApos : 0 < Real.log A := by linarith
    have hlogAle : Real.log A ≤ 2 * Real.log B := by
      have h : Real.log A ≤ Real.log (B ^ 2) := Real.log_le_log hApos hABsq
      have h2 : Real.log (B ^ 2) = 2 * Real.log B := by rw [Real.log_pow]; norm_num
      linarith [h, h2]
    have hDpos : 0 < Real.sqrt (Real.log A) := Real.sqrt_pos.mpr hlogApos
    have hEpos : 0 < Real.sqrt (Real.log B) := Real.sqrt_pos.mpr hlogBpos
    -- √(log A) ≤ 2 √(log B)
    have hsq : Real.sqrt (Real.log A) ≤ 2 * Real.sqrt (Real.log B) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have hb : Real.sqrt (Real.log B) ^ 2 = Real.log B := Real.sq_sqrt (le_of_lt hlogBpos)
      nlinarith [hb, hlogAle, hlogB2]
    have hA14pos : 0 < A ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hApos _
    have hA14 : Real.sqrt (Real.log A) ≤ A ^ ((1 : ℝ) / 4) := sqrt_log_le_rpow_quarter hA1
    -- term 1
    have ht1 : k1 / A ^ ((1 : ℝ) / 4) ≤ |k1| / Real.sqrt (Real.log A) := by
      calc k1 / A ^ ((1 : ℝ) / 4) ≤ |k1| / A ^ ((1 : ℝ) / 4) :=
            div_le_div_of_nonneg_right (le_abs_self k1) (le_of_lt hA14pos)
        _ ≤ |k1| / Real.sqrt (Real.log A) :=
            div_le_div_of_nonneg_left (abs_nonneg k1) hDpos hA14
    -- term 2
    have ht2 : k2 / Real.sqrt (Real.log B) ≤ 2 * |k2| / Real.sqrt (Real.log A) := by
      have step1 : k2 / Real.sqrt (Real.log B) ≤ |k2| / Real.sqrt (Real.log B) :=
        div_le_div_of_nonneg_right (le_abs_self k2) (le_of_lt hEpos)
      have hcb : Real.sqrt (Real.log A) / 2 ≤ Real.sqrt (Real.log B) := by linarith [hsq]
      have step2 : |k2| / Real.sqrt (Real.log B) ≤ |k2| / (Real.sqrt (Real.log A) / 2) :=
        div_le_div_of_nonneg_left (abs_nonneg k2) (by linarith) hcb
      have step3 : |k2| / (Real.sqrt (Real.log A) / 2) = 2 * |k2| / Real.sqrt (Real.log A) := by
        rw [div_div_eq_mul_div]; ring
      linarith [step1, step2, step3.le]
    -- term 3
    have hDAle : Real.sqrt (Real.log A) ≤ Real.log A := by
      rw [Real.sqrt_le_iff]
      refine ⟨by linarith, ?_⟩
      nlinarith [hlogA53]
    have ht3 : C / Real.log A ≤ |C| / Real.sqrt (Real.log A) := by
      calc C / Real.log A ≤ |C| / Real.log A :=
            div_le_div_of_nonneg_right (le_abs_self C) (le_of_lt hlogApos)
        _ ≤ |C| / Real.sqrt (Real.log A) :=
            div_le_div_of_nonneg_left (abs_nonneg C) hDpos hDAle
    have hKD : k1 / A ^ ((1 : ℝ) / 4) + k2 / Real.sqrt (Real.log B) + C / Real.log A
        ≤ (|k1| + 2 * |k2| + |C|) / Real.sqrt (Real.log A) := by
      have hsum := add_le_add (add_le_add ht1 ht2) ht3
      have heq : (|k1| / Real.sqrt (Real.log A) + 2 * |k2| / Real.sqrt (Real.log A))
            + |C| / Real.sqrt (Real.log A)
          = (|k1| + 2 * |k2| + |C|) / Real.sqrt (Real.log A) := by ring
      linarith [hsum, heq.le]
    have hup : (|k1| + 2 * |k2| + |C|) / Real.sqrt (Real.log A)
        ≤ (|k1| + 2 * |k2| + |C| + 1) / Real.sqrt (Real.log A) :=
      div_le_div_of_nonneg_right
        (by linarith [abs_nonneg k1, abs_nonneg k2, abs_nonneg C]) (le_of_lt hDpos)
    refine ⟨hApos, hBpos, hlogApos, ?_⟩
    simp only [Real.sqrt_eq_rpow] at hKD hup
    linarith [hKD, hup]

end Work.HP.MM2
