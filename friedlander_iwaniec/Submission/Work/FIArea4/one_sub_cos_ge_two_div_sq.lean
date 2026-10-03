import Mathlib
import Submission.Work.FIArea4.logSine_defs

namespace Work.FIArea4

/-- `1 - cos α ≥ 2/N²` for `α` at least `5/(2N)` (the crossover point of the log-sine mollifier
`Psi N`), and `α ≤ π/2`, `N ≥ 3`.  Case `α ≤ 1` uses `1 - cos x ≥ (43/96)x²`; case `α ≥ 1`
uses `1 - cos α ≥ 1 - cos 1 ≥ 43/96 ≥ 2/N²`. -/
theorem one_sub_cos_ge_two_div_sq (N : ℕ) (hN : 3 ≤ N) {α : ℝ}
    (h1 : 5 / (2 * (N:ℝ)) ≤ α) (h2 : α ≤ Real.pi / 2) :
    2 / (N:ℝ)^2 ≤ 1 - Real.cos α := by
  have hN3 : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by positivity
  have hN1 : (1:ℝ) ≤ N := by linarith
  have hαpos : 0 < α := lt_of_lt_of_le (by positivity) h1
  -- `2/N² ≤ 43/96`
  have hbase : 2 / (N:ℝ)^2 ≤ 43/96 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (N:ℝ)^2)]
    have h9 : (9:ℝ) ≤ (N:ℝ)^2 := by nlinarith
    nlinarith
  by_cases hα1 : α ≤ 1
  · -- case `α ≤ 1`: use the `(43/96)x²` lower bound on `1 - cos x`
    have hx : |α| ≤ 1 := by rw [abs_of_pos hαpos]; exact hα1
    have h43 := one_sub_cos_ge hx
    have hα2 : (5 / (2 * (N:ℝ)))^2 ≤ α^2 := pow_le_pow_left₀ (by positivity) h1 2
    have hmono : (43/96) * (5 / (2 * (N:ℝ)))^2 ≤ (43/96) * α^2 :=
      mul_le_mul_of_nonneg_left hα2 (by norm_num)
    have heq : (43/96) * (5 / (2 * (N:ℝ)))^2 = 1075 / (384 * (N:ℝ)^2) := by
      field_simp; ring
    have hkey : 2 / (N:ℝ)^2 ≤ (43/96) * (5 / (2 * (N:ℝ)))^2 := by
      rw [heq, div_le_div_iff₀ (by positivity : (0:ℝ) < (N:ℝ)^2)
            (by positivity : (0:ℝ) < 384 * (N:ℝ)^2)]
      nlinarith
    linarith
  · -- case `1 < α`: `cos α ≤ cos 1`, so `1 - cos α ≥ 1 - cos 1 ≥ 43/96 ≥ 2/N²`
    have hcos : Real.cos α ≤ Real.cos 1 :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num)
        (by linarith [Real.pi_pos, h2]) (not_le.mp hα1).le
    have h43 : (43/96:ℝ) ≤ 1 - Real.cos α := by
      have h := one_sub_cos_ge (x := (1:ℝ)) (by norm_num)
      norm_num at h
      linarith
    linarith

end Work.FIArea4
