import Mathlib
import Submission.Commons.Analysis.Asymptotics.log_add_one_rpow_le_mul_rpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Asymptotics

/-- Quantitative sub-polynomial growth: for `0 ≤ A` and `0 < b` there is a constant
`C > 0` with `(log x + 2)^A ≤ C * x^b` for every `x ≥ 2`. -/
lemma exists_log_add_two_rpow_le_mul_rpow {A b : ℝ} (hA : 0 ≤ A) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x → (Real.log x + 2) ^ A ≤ C * x ^ b := by
  obtain ⟨C₁, hC₁, h₁⟩ := log_add_one_rpow_le_mul_rpow hA hb
  have h2A : 0 < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  refine ⟨(2 : ℝ) ^ A * C₁, mul_pos h2A hC₁, ?_⟩
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hbase : 0 ≤ Real.log x + 2 := by linarith
  have hbase2 : 0 ≤ 2 * (Real.log x + 1) := by linarith
  have hle : Real.log x + 2 ≤ 2 * (Real.log x + 1) := by linarith
  calc
    (Real.log x + 2) ^ A ≤ (2 * (Real.log x + 1)) ^ A :=
          Real.rpow_le_rpow hbase hle hA
    _ = (2 : ℝ) ^ A * (Real.log x + 1) ^ A :=
          Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ (2 : ℝ) ^ A * (C₁ * x ^ b) :=
          mul_le_mul_of_nonneg_left (h₁ x hx1) (le_of_lt h2A)
    _ = ((2 : ℝ) ^ A * C₁) * x ^ b := by ring

theorem pow_const_le_mul_rpow {a b : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K m : ℕ), 2 ≤ m →
      (K : ℝ) ≤ 2 + L * (Real.log (Real.log (m : ℝ) + 2) + 1) →
      a ^ K ≤ C * (m : ℝ) ^ b := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hlogA : 0 ≤ Real.log a := Real.log_nonneg ha
  have hA : 0 ≤ L * Real.log a := mul_nonneg hL hlogA
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    exists_log_add_two_rpow_le_mul_rpow (A := L * Real.log a) hA hb
  have hpos : 0 < a ^ (2 + L) := Real.rpow_pos_of_pos ha0 _
  refine ⟨a ^ (2 + L) * C₀, mul_pos hpos hC₀pos, ?_⟩
  intro K m hm hK
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hu : 0 < Real.log (m : ℝ) + 2 := by linarith
  -- the key rewriting of the exponential bound as a power of `log m + 2`
  have key : a ^ (2 + L * (Real.log (Real.log (m : ℝ) + 2) + 1))
      = a ^ (2 + L) * (Real.log (m : ℝ) + 2) ^ (L * Real.log a) := by
    rw [show 2 + L * (Real.log (Real.log (m : ℝ) + 2) + 1)
          = (2 + L) + L * Real.log (Real.log (m : ℝ) + 2) by ring]
    rw [Real.rpow_add ha0]
    congr 1
    rw [Real.rpow_def_of_pos ha0, Real.rpow_def_of_pos hu]
    congr 1
    ring
  calc
    a ^ K = a ^ (K : ℝ) := (Real.rpow_natCast a K).symm
    _ ≤ a ^ (2 + L * (Real.log (Real.log (m : ℝ) + 2) + 1)) :=
          Real.rpow_le_rpow_of_exponent_le ha hK
    _ = a ^ (2 + L) * (Real.log (m : ℝ) + 2) ^ (L * Real.log a) := key
    _ ≤ a ^ (2 + L) * (C₀ * (m : ℝ) ^ b) :=
          mul_le_mul_of_nonneg_left (hC₀ (m : ℝ) hm2) (le_of_lt hpos)
    _ = (a ^ (2 + L) * C₀) * (m : ℝ) ^ b := by ring

end Commons.Analysis.Asymptotics
