import Mathlib
import Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- For all sufficiently large `b`, if `0 < h ≤ b` and `8b/(log b)² ≤ h`, then the Chebyshev
`θ`-increase over `(b, b+h]` is at least `5h/8`.  Intended proof: import
`Submission.Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog` (i.e.
`∃ x₀, ∀ x ≥ x₀, |θ x - x| ≤ x/(log x)²`) with `A = 2`, take `X = max x₀ (exp 4)`, and combine
`θ b ≤ b + b/log²b`, `θ (b+h) ≥ (b+h) - (b+h)/log²(b+h)` with `log²(b+h) ≥ log²b ≥ 16`. -/
theorem theta_window_increment_lower :
    ∃ X : ℝ, ∀ b h : ℝ, X ≤ b → 0 < h → h ≤ b →
      8 * b / (Real.log b) ^ 2 ≤ h →
      (5 / 8) * h ≤ Chebyshev.theta (b + h) - Chebyshev.theta b := by
  obtain ⟨x₀, hx₀⟩ :=
    Commons.NumberTheory.PrimeNumberTheorem.theta_sub_id_powLog 2 (by norm_num)
  refine ⟨max x₀ (Real.exp 4), ?_⟩
  intro b h hX hh hhb hh8
  have hx₀b : x₀ ≤ b := le_trans (le_max_left _ _) hX
  have hexp : Real.exp 4 ≤ b := le_trans (le_max_right _ _) hX
  have hbpos : 0 < b := lt_of_lt_of_le (Real.exp_pos 4) hexp
  have hbhpos : 0 < b + h := by linarith
  have hlog4 : (4 : ℝ) ≤ Real.log b := by
    rw [Real.le_log_iff_exp_le hbpos]; exact hexp
  have hlogbpos : 0 < Real.log b := by linarith
  have hlogmono : Real.log b ≤ Real.log (b + h) :=
    Real.log_le_log hbpos (by linarith)
  have hlogbhpos : 0 < Real.log (b + h) := lt_of_lt_of_le hlogbpos hlogmono
  have hx₀bh : x₀ ≤ b + h := le_trans hx₀b (by linarith)
  have hb1 : |Chebyshev.theta b - b| ≤ b / (Real.log b) ^ 2 := by
    have h := hx₀ b hx₀b
    rw [Real.rpow_two] at h
    exact h
  have hb2 : |Chebyshev.theta (b + h) - (b + h)| ≤
      (b + h) / (Real.log (b + h)) ^ 2 := by
    have h := hx₀ (b + h) hx₀bh
    rw [Real.rpow_two] at h
    exact h
  have hble : Chebyshev.theta b ≤ b + b / (Real.log b) ^ 2 := by
    have := (abs_le.mp hb1).2
    linarith
  have hbhge : b + h - (b + h) / (Real.log (b + h)) ^ 2 ≤ Chebyshev.theta (b + h) := by
    have := (abs_le.mp hb2).1
    linarith
  have hDle : (Real.log b) ^ 2 ≤ (Real.log (b + h)) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hlogbpos) hlogmono 2
  have hden1 : 0 < (Real.log b) ^ 2 := pow_pos hlogbpos 2
  have hden2 : 0 < (Real.log (b + h)) ^ 2 := pow_pos hlogbhpos 2
  have hfrac : (b + h) / (Real.log (b + h)) ^ 2 ≤ 2 * (b / (Real.log b) ^ 2) := by
    rw [show 2 * (b / (Real.log b) ^ 2) = 2 * b / (Real.log b) ^ 2 by ring]
    rw [div_le_div_iff₀ hden2 hden1]
    have hN : b + h ≤ 2 * b := by linarith
    calc (b + h) * (Real.log b) ^ 2 ≤ (2 * b) * (Real.log b) ^ 2 :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ ≤ (2 * b) * (Real.log (b + h)) ^ 2 :=
          mul_le_mul_of_nonneg_left hDle (by linarith)
  have hbfrac : b / (Real.log b) ^ 2 ≤ h / 8 := by
    have heq : 8 * b / (Real.log b) ^ 2 = 8 * (b / (Real.log b) ^ 2) := by ring
    rw [heq] at hh8
    linarith
  have hkey : h - 3 * (b / (Real.log b) ^ 2) ≤
      Chebyshev.theta (b + h) - Chebyshev.theta b := by linarith
  have hfin : (5 / 8) * h ≤ h - 3 * (b / (Real.log b) ^ 2) := by linarith
  linarith

end Work.BMF.SD
