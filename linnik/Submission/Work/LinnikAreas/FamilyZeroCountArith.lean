import Mathlib

namespace Work.LinnikAreas

/-- For `ε > 0` and `x ≥ 1`:
`x * (log x + 2) ≤ (1/ε + 2) * x ^ (1 + ε)`.

Indeed `log x ≤ x^ε / ε` and `1 ≤ x^ε` give `log x + 2 ≤ (1/ε + 2) * x^ε`, and
multiplying by `x ≥ 0` and using `x * x^ε = x^(1+ε)` finishes. -/
lemma mul_log_add_two_le {ε x : ℝ} (hε : 0 < ε) (hx : 1 ≤ x) :
    x * (Real.log x + 2) ≤ (1/ε + 2) * x ^ (1 + ε) := by
  have hxpos : 0 < x := by linarith
  have hlog : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div hxpos.le hε
  have hxε1 : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have heq : x ^ ε / ε = (1/ε) * x ^ ε := by ring
  rw [heq] at hlog
  have hsum : Real.log x + 2 ≤ (1/ε + 2) * x ^ ε := by
    have h2 : (2:ℝ) ≤ 2 * x ^ ε := by linarith
    nlinarith [hlog, h2]
  calc x * (Real.log x + 2) ≤ x * ((1/ε + 2) * x ^ ε) :=
        mul_le_mul_of_nonneg_left hsum hxpos.le
    _ = (1/ε + 2) * x ^ (1 + ε) := by
        rw [Real.rpow_add hxpos, Real.rpow_one]; ring

/-- Growth estimate: for every `ε > 0` the quantity
`q · (T+2) · (log (q · (T+2)) + 2)` is bounded by a constant times
`(q · T)^(1+ε)`, uniformly over all `q ≥ 2` and all real `T ≥ 1`. -/
theorem FamilyZeroCountArith (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ T : ℝ, 1 ≤ T →
      (q : ℝ) * (T + 2) * (Real.log ((q : ℝ) * (T + 2)) + 2)
        ≤ C * ((q : ℝ) * T) ^ (1 + ε) := by
  refine ⟨(1/ε + 2) * 3 ^ (1 + ε), by positivity, ?_⟩
  intro q hq T hT
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hTpos : (0:ℝ) < T := by linarith
  set x : ℝ := (q:ℝ) * T with hxdef
  set y : ℝ := (q:ℝ) * (T + 2) with hydef
  have hxpos : 0 < x := by rw [hxdef]; positivity
  have hypos : 0 < y := by rw [hydef]; positivity
  have hx1 : 1 ≤ x := by
    rw [hxdef]
    have h : (2:ℝ) * 1 ≤ (q:ℝ) * T :=
      mul_le_mul hq2 hT (by norm_num) (by linarith : (0:ℝ) ≤ (q:ℝ))
    linarith
  have hy1 : 1 ≤ y := by
    rw [hydef]
    have h : (2:ℝ) * 3 ≤ (q:ℝ) * (T + 2) :=
      mul_le_mul hq2 (by linarith : (3:ℝ) ≤ T + 2) (by norm_num) (by linarith : (0:ℝ) ≤ (q:ℝ))
    linarith
  have hy3x : y ≤ 3 * x := by
    rw [hydef, hxdef]
    have h : (q:ℝ) * 1 ≤ (q:ℝ) * T := mul_le_mul_of_nonneg_left hT (by linarith : (0:ℝ) ≤ (q:ℝ))
    nlinarith [h]
  have h1 := mul_log_add_two_le hε hy1
  have h2 : y ^ (1+ε) ≤ (3*x) ^ (1+ε) := Real.rpow_le_rpow hypos.le hy3x (by linarith)
  have h3 : (3*x)^(1+ε) = 3^(1+ε) * x^(1+ε) := Real.mul_rpow (by norm_num) hxpos.le
  calc (q:ℝ) * (T + 2) * (Real.log ((q:ℝ) * (T + 2)) + 2)
      = y * (Real.log y + 2) := by rw [← hydef]
    _ ≤ (1/ε + 2) * y ^ (1+ε) := h1
    _ ≤ (1/ε + 2) * (3 * x) ^ (1+ε) := by
          apply mul_le_mul_of_nonneg_left h2; positivity
    _ = (1/ε + 2) * 3 ^ (1+ε) * x ^ (1+ε) := by rw [h3]; ring
    _ = (1/ε + 2) * 3 ^ (1+ε) * ((q:ℝ)*T) ^ (1+ε) := by rw [hxdef]

end Work.LinnikAreas
