import Mathlib

namespace Work.Commons.NumberTheory.Moebius

open scoped BigOperators

/--
Core logarithm-power estimate: for `x ≥ 1` and positive real exponents `A, δ`,
`(log x)^A ≤ (A/δ)^A * x^δ`.
This follows from `Real.log x ≤ x^ε / ε` with `ε = δ / A`.
-/
lemma log_rpow_le_mul_rpow (A δ : ℝ) (hA : 0 < A) (hδ : 0 < δ) {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x)^A ≤ (A/δ)^A * x^δ := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
  have hlog : Real.log x ≤ x^(δ/A) / (δ/A) :=
    Real.log_le_rpow_div hx0.le (div_pos hδ hA)
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : (Real.log x)^A ≤ (x^(δ/A) / (δ/A))^A :=
    Real.rpow_le_rpow hlog0 hlog hA.le
  have h2 : (x^(δ/A) / (δ/A))^A = (A/δ)^A * x^δ := by
    rw [div_eq_mul_inv,
        Real.mul_rpow (Real.rpow_nonneg hx0.le _) (inv_nonneg.mpr (div_pos hδ hA).le)]
    rw [← Real.rpow_mul hx0.le]
    have hmul : δ/A * A = δ := by field_simp
    rw [hmul, inv_div]
    ring
  rw [h2] at h1
  exact h1

theorem log_pow_bookkeeping (A : ℝ) (hA : 0 < A) :
    (∃ K : ℝ, 0 < K ∧ ∀ Q : ℝ, 1 ≤ Q →
        (Real.sqrt Q)⁻¹ ≤ K * (Real.log (2 + Q)) ^ (-A)) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ Q : ℝ, 1 ≤ Q →
        (Real.log 2) ^ (-A) * (Real.sqrt (Real.sqrt Q))⁻¹ ≤ K * (Real.log (2 + Q)) ^ (-A)) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ Q : ℝ, 1 ≤ Q →
        (Real.log (2 + Real.sqrt Q)) ^ (-A) ≤ K * (Real.log (2 + Q)) ^ (-A)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: `(√Q)⁻¹ ≤ K (log(2+Q))^{-A}`, with `K = (2A)^A √3`.
    refine ⟨(2*A)^A * Real.sqrt 3, by positivity, ?_⟩
    intro Q hQ
    have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ
    have h2Q : 1 ≤ 2 + Q := by linarith
    have hlogpos : 0 < Real.log (2+Q) := Real.log_pos (by linarith)
    have hcore : (Real.log (2 + Q))^A ≤ (2*A)^A * (2 + Q)^((1:ℝ)/2) := by
      have h := log_rpow_le_mul_rpow A ((1:ℝ)/2) hA (by norm_num) h2Q
      have h' : A / ((1:ℝ)/2) = 2*A := by ring
      rw [h'] at h
      exact h
    have hsqle : (2 + Q)^((1:ℝ)/2) ≤ Real.sqrt 3 * Real.sqrt Q := by
      have hle : (2 + Q) ≤ 3 * Q := by linarith
      have h1 : (2 + Q)^((1:ℝ)/2) ≤ (3*Q)^((1:ℝ)/2) :=
        Real.rpow_le_rpow (by linarith) hle (by norm_num)
      have h2 : (3*Q)^((1:ℝ)/2) = Real.sqrt 3 * Real.sqrt Q := by
        rw [Real.mul_rpow (by norm_num) hQpos.le, ← Real.sqrt_eq_rpow 3, ← Real.sqrt_eq_rpow Q]
      exact le_trans h1 (le_of_eq h2)
    have hmain : (Real.log (2 + Q))^A ≤ (2*A)^A * Real.sqrt 3 * Real.sqrt Q := by
      calc (Real.log (2 + Q))^A ≤ (2*A)^A * (Real.sqrt 3 * Real.sqrt Q) :=
            le_trans hcore (mul_le_mul_of_nonneg_left hsqle (by positivity))
        _ = (2*A)^A * Real.sqrt 3 * Real.sqrt Q := by ring
    have hLpos : 0 < (Real.log (2+Q))^A := Real.rpow_pos_of_pos hlogpos A
    rw [Real.rpow_neg hlogpos.le A]
    rw [le_mul_inv_iff₀ hLpos]
    have hsqne : Real.sqrt Q ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hQpos)
    calc (Real.sqrt Q)⁻¹ * (Real.log (2+Q))^A
        = (Real.log (2+Q))^A * (Real.sqrt Q)⁻¹ := by ring
      _ ≤ ((2*A)^A * Real.sqrt 3 * Real.sqrt Q) * (Real.sqrt Q)⁻¹ :=
          mul_le_mul_of_nonneg_right hmain (inv_nonneg.mpr (Real.sqrt_nonneg Q))
      _ = (2*A)^A * Real.sqrt 3 := by
          rw [mul_assoc, mul_inv_cancel₀ hsqne, mul_one]
  · -- Part 2: `(log 2)^{-A} (√√Q)⁻¹ ≤ K (log(2+Q))^{-A}`, with `K = (log 2)^{-A} (4A)^A 3^{1/4}`.
    refine ⟨(Real.log 2)^(-A) * ((4*A)^A * 3^((1:ℝ)/4)), by positivity, ?_⟩
    intro Q hQ
    have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ
    have h2Q : 1 ≤ 2 + Q := by linarith
    have hlogpos : 0 < Real.log (2+Q) := Real.log_pos (by linarith)
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hss : Real.sqrt (Real.sqrt Q) = Q^((1:ℝ)/4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hQpos.le]
      norm_num
    have hcore : (Real.log (2 + Q))^A ≤ (4*A)^A * (2 + Q)^((1:ℝ)/4) := by
      have h := log_rpow_le_mul_rpow A ((1:ℝ)/4) hA (by norm_num) h2Q
      have h' : A / ((1:ℝ)/4) = 4*A := by ring
      rw [h'] at h
      exact h
    have hsqle : (2 + Q)^((1:ℝ)/4) ≤ 3^((1:ℝ)/4) * Q^((1:ℝ)/4) := by
      have hle : (2 + Q) ≤ 3 * Q := by linarith
      have h1 : (2 + Q)^((1:ℝ)/4) ≤ (3*Q)^((1:ℝ)/4) :=
        Real.rpow_le_rpow (by linarith) hle (by norm_num)
      have h2 : (3*Q)^((1:ℝ)/4) = 3^((1:ℝ)/4) * Q^((1:ℝ)/4) := by
        rw [Real.mul_rpow (by norm_num) hQpos.le]
      exact le_trans h1 (le_of_eq h2)
    have hmain : (Real.log (2 + Q))^A ≤ (4*A)^A * 3^((1:ℝ)/4) * Real.sqrt (Real.sqrt Q) := by
      calc (Real.log (2+Q))^A ≤ (4*A)^A * (3^((1:ℝ)/4) * Q^((1:ℝ)/4)) :=
            le_trans hcore (mul_le_mul_of_nonneg_left hsqle (by positivity))
        _ = (4*A)^A * 3^((1:ℝ)/4) * Real.sqrt (Real.sqrt Q) := by rw [← hss]; ring
    have hSpos : 0 < Real.sqrt (Real.sqrt Q) := Real.sqrt_pos_of_pos (Real.sqrt_pos_of_pos hQpos)
    have hLpos : 0 < (Real.log (2+Q))^A := Real.rpow_pos_of_pos hlogpos A
    have hapos : 0 ≤ (Real.log 2)^(-A) := (Real.rpow_pos_of_pos hlog2pos _).le
    rw [Real.rpow_neg hlogpos.le A]
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    rw [div_le_div_iff₀ hSpos hLpos]
    exact le_trans (mul_le_mul_of_nonneg_left hmain hapos) (le_of_eq (by ring))
  · -- Part 3: `(log(2+√Q))^{-A} ≤ K (log(2+Q))^{-A}`, with `K = 2^A`.
    refine ⟨2^A, by positivity, ?_⟩
    intro Q hQ
    have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ
    have hm : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg Q
    have hlogpos : 0 < Real.log (2+Q) := Real.log_pos (by linarith)
    have hlogpos2 : 0 < Real.log (2 + Real.sqrt Q) := Real.log_pos (by linarith)
    have hle : 2 + Q ≤ (2 + Real.sqrt Q)^2 := by
      have hsq : (Real.sqrt Q)^2 = Q := Real.sq_sqrt hQpos.le
      nlinarith [hsq, hm]
    have hlog_le : Real.log (2+Q) ≤ 2 * Real.log (2 + Real.sqrt Q) := by
      have h1 : Real.log (2+Q) ≤ Real.log ((2 + Real.sqrt Q)^2) :=
        Real.log_le_log (by linarith) hle
      have h2 : Real.log ((2 + Real.sqrt Q)^2) = 2 * Real.log (2 + Real.sqrt Q) := by
        rw [Real.log_pow]; push_cast; ring
      linarith [h1, h2]
    have hmain : (Real.log (2+Q))^A ≤ 2^A * (Real.log (2 + Real.sqrt Q))^A := by
      have h := Real.rpow_le_rpow hlogpos.le hlog_le hA.le
      rwa [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hlogpos2.le] at h
    have hMpos : 0 < (Real.log (2 + Real.sqrt Q))^A := Real.rpow_pos_of_pos hlogpos2 A
    have hLpos : 0 < (Real.log (2+Q))^A := Real.rpow_pos_of_pos hlogpos A
    rw [Real.rpow_neg hlogpos.le A, Real.rpow_neg hlogpos2.le A]
    rw [le_mul_inv_iff₀ hLpos]
    calc ((Real.log (2 + Real.sqrt Q))^A)⁻¹ * (Real.log (2+Q))^A
        = (Real.log (2+Q))^A * ((Real.log (2 + Real.sqrt Q))^A)⁻¹ := by ring
      _ ≤ (2^A * (Real.log (2 + Real.sqrt Q))^A) * ((Real.log (2 + Real.sqrt Q))^A)⁻¹ :=
          mul_le_mul_of_nonneg_right hmain (inv_nonneg.mpr hMpos.le)
      _ = 2^A := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hMpos), mul_one]

end Work.Commons.NumberTheory.Moebius
