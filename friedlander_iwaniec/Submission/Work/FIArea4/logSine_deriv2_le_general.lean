import Mathlib
import Submission.Work.FIArea4.logSine_deriv2_base
import Submission.Work.FIArea4.logSine_psi_global_bound
import Submission.Work.FIArea4.logSine_psi_deriv
import Submission.Work.FIArea4.logSine_defs

namespace Work.FIArea4

open scoped Topology
open scoped ContDiff

/-- Pointwise bound for `u_N''` on `[0, π/2]` using the *global* bounds for `Ψ_N'` and `Ψ_N''`
(valid at every `y ≥ 0`, `logSine_psi_global_bound`) together with the exact value `1/(2h)`,
`1/(2h²)` for `h = 1 + cos α ≥ 1 ≥ 2/N²`.  Note `sin²α = (1-cos α)(1+cos α) ≤ α²·1`. -/
theorem logSine_deriv2_le_general (N : ℕ) (hN : 2 ≤ N) (K : ℝ) (hK : 1 ≤ K)
    (hK1 : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ K)
    (hK2 : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ K) {α : ℝ}
    (hα0 : 0 ≤ α) (hαp : α ≤ Real.pi / 2) :
    |deriv (deriv (ufun N)) α| ≤ 4 * K * (N:ℝ)^2 * (Real.log N + 1)
      + 8 * K * (N:ℝ)^4 * (Real.log N + 1) * α^2 + 1 := by
  have hN1 : 1 ≤ N := by omega
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  -- `cos α ≥ 0` on `[0, π/2]`
  have hcosnn : 0 ≤ Real.cos α :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos, hα0]) hαp
  have hge1 : (1:ℝ) ≤ 1 + Real.cos α := by linarith
  have hpos : (0:ℝ) < 1 + Real.cos α := by linarith
  -- `h = 1 + cos α` lies above the transition window
  have hy2 : 2 / (N:ℝ)^2 ≤ 1 + Real.cos α := by
    have h2N : 2 / (N:ℝ)^2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  -- `1 - cos α ≥ 0`, so the *global* bound for `Ψ'`, `Ψ''` applies there
  have hy1 : (0:ℝ) ≤ 1 - Real.cos α := by linarith [Real.cos_le_one α]
  obtain ⟨hP1, hP2, -, -, -⟩ := logSine_psi_deriv N hN K hK hK1 hK2
  obtain ⟨hGlob1, hGlob2⟩ := logSine_psi_global_bound N hN K hK hK1 hK2
  have hA : deriv (Psi N) (1 + Real.cos α) = 1 / (2 * (1 + Real.cos α)) := hP1 _ hy2
  have hB : deriv (deriv (Psi N)) (1 + Real.cos α) = -(1 / (2 * (1 + Real.cos α)^2)) :=
    hP2 _ hy2
  have hsin : Real.sin α ^ 2 ≤ α ^ 2 := Real.sin_sq_le_sq
  have hcos1 : |Real.cos α| ≤ 1 := Real.abs_cos_le_one α
  -- The exact algebraic shape of `u_N''`, using the exact values at `1 + cos α`.
  -- The two "exact" contributions combine into `1/(2h)`:
  -- `cos α/(2h) + sin²α/(2h²) = (cos α·h + sin²α)/(2h²) = h/(2h²) = 1/(2h)`.
  have key : deriv (deriv (ufun N)) α
      = 1 / (2 * (1 + Real.cos α)) - Real.cos α * deriv (Psi N) (1 - Real.cos α)
        - Real.sin α ^ 2 * deriv (deriv (Psi N)) (1 - Real.cos α) := by
    rw [deriv_deriv_ufun_eq N hN1]
    simp only [hA, hB]
    field_simp
    nlinarith [Real.sin_sq α]
  have hbound : |1 / (2 * (1 + Real.cos α)) - Real.cos α * deriv (Psi N) (1 - Real.cos α)
        - Real.sin α ^ 2 * deriv (deriv (Psi N)) (1 - Real.cos α)|
      ≤ 1 / (2 * (1 + Real.cos α))
        + |Real.cos α| * |deriv (Psi N) (1 - Real.cos α)|
        + Real.sin α ^ 2 * |deriv (deriv (Psi N)) (1 - Real.cos α)| := by
    have e1 := abs_sub (1 / (2 * (1 + Real.cos α)) - Real.cos α * deriv (Psi N) (1 - Real.cos α))
      (Real.sin α ^ 2 * deriv (deriv (Psi N)) (1 - Real.cos α))
    have e2 := abs_sub (1 / (2 * (1 + Real.cos α))) (Real.cos α * deriv (Psi N) (1 - Real.cos α))
    have e3 : |1 / (2 * (1 + Real.cos α))| = 1 / (2 * (1 + Real.cos α)) :=
      abs_of_pos (by positivity)
    have e4 : |Real.cos α * deriv (Psi N) (1 - Real.cos α)|
        = |Real.cos α| * |deriv (Psi N) (1 - Real.cos α)| := abs_mul _ _
    have e5 : |Real.sin α ^ 2 * deriv (deriv (Psi N)) (1 - Real.cos α)|
        = Real.sin α ^ 2 * |deriv (deriv (Psi N)) (1 - Real.cos α)| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    rw [e3, e4] at e2
    rw [e5] at e1
    linarith
  have hterm1 : |Real.cos α| * |deriv (Psi N) (1 - Real.cos α)|
      ≤ 4 * K * (N:ℝ)^2 * (Real.log N + 1) := by
    have hP := hGlob1 (1 - Real.cos α) hy1
    have h := mul_le_mul hcos1 hP (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    simpa using h
  have hterm2 : Real.sin α ^ 2 * |deriv (deriv (Psi N)) (1 - Real.cos α)|
      ≤ α ^ 2 * (8 * K * (N:ℝ)^4 * (Real.log N + 1)) := by
    have hQ := hGlob2 (1 - Real.cos α) hy1
    exact mul_le_mul hsin hQ (abs_nonneg _) (sq_nonneg α)
  have hhalf : 1 / (2 * (1 + Real.cos α)) ≤ 1 / 2 := by
    have h := one_div_le_one_div_of_le (show (0:ℝ) < 2 by norm_num)
      (by linarith : (2:ℝ) ≤ 2 * (1 + Real.cos α))
    simpa using h
  calc |deriv (deriv (ufun N)) α|
      = |1 / (2 * (1 + Real.cos α)) - Real.cos α * deriv (Psi N) (1 - Real.cos α)
          - Real.sin α ^ 2 * deriv (deriv (Psi N)) (1 - Real.cos α)| := by rw [key]
    _ ≤ 1 / (2 * (1 + Real.cos α)) + |Real.cos α| * |deriv (Psi N) (1 - Real.cos α)|
        + Real.sin α ^ 2 * |deriv (deriv (Psi N)) (1 - Real.cos α)| := hbound
    _ ≤ 1 / 2 + 4 * K * (N:ℝ)^2 * (Real.log N + 1)
        + α ^ 2 * (8 * K * (N:ℝ)^4 * (Real.log N + 1)) := by linarith
    _ ≤ 4 * K * (N:ℝ)^2 * (Real.log N + 1)
        + 8 * K * (N:ℝ)^4 * (Real.log N + 1) * α ^ 2 + 1 := by nlinarith

end Work.FIArea4
