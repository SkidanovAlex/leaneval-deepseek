import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.gRHSBound

/-- The coefficient `μ + lam + μ·lam` of `D_z g` in `N_*` is bounded by `2` under the
modulation hypotheses `|μ| ≤ 1/2`, `|lam| ≤ 1`. -/
private theorem abs_modCoeff_le {μ lam : ℝ} (hμ : |μ| ≤ 1 / 2) (hlam : |lam| ≤ 1) :
    |μ + lam + μ * lam| ≤ 2 := by
  have h1 : |μ + lam| ≤ |μ| + |lam| := abs_add_le μ lam
  have h2 : |μ * lam| = |μ| * |lam| := abs_mul μ lam
  have hμ0 : (0 : ℝ) ≤ |μ| := abs_nonneg μ
  have hl0 : (0 : ℝ) ≤ |lam| := abs_nonneg lam
  have h3 : |μ| * |lam| ≤ (1 / 2) * 1 := mul_le_mul hμ hlam hl0 (by norm_num)
  calc |μ + lam + μ * lam| ≤ |μ + lam| + |μ * lam| := abs_add_le (μ + lam) (μ * lam)
    _ ≤ (|μ| + |lam|) + |μ| * |lam| := by rw [h2]; exact add_le_add h1 le_rfl
    _ ≤ 2 := by linarith

theorem abs_Nstar_le {μ lam B : ℝ} (hB : 0 ≤ B) (hμ : |μ| ≤ 1 / 2) (hlam : |lam| ≤ 1)
    {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hgb : |g z θ| ≤ B)
    (hDzgb : |Work.Spaces.Dz g z θ| ≤ B) :
    |Work.Construction.Nstar μ lam g z θ| ≤ 3 * B := by
  have hc : |μ + lam + μ * lam| ≤ 2 := abs_modCoeff_le hμ hlam
  have hg0 : (0 : ℝ) ≤ |g z θ| := abs_nonneg _
  have hd0 : (0 : ℝ) ≤ |Work.Spaces.Dz g z θ| := abs_nonneg _
  have h1 : |μ| * |g z θ| ≤ (1 / 2) * B := mul_le_mul hμ hgb hg0 (by norm_num)
  have h2 : |μ + lam + μ * lam| * |Work.Spaces.Dz g z θ| ≤ 2 * B :=
    mul_le_mul hc hDzgb hd0 (by norm_num)
  have hstep : |-μ * g z θ - (μ + lam + μ * lam) * Work.Spaces.Dz g z θ|
      ≤ |μ| * |g z θ| + |μ + lam + μ * lam| * |Work.Spaces.Dz g z θ| := by
    calc |-μ * g z θ - (μ + lam + μ * lam) * Work.Spaces.Dz g z θ|
        ≤ |-μ * g z θ| + |(μ + lam + μ * lam) * Work.Spaces.Dz g z θ| := by
          simpa using abs_sub_le (-μ * g z θ) 0 ((μ + lam + μ * lam) * Work.Spaces.Dz g z θ)
      _ = |μ| * |g z θ| + |μ + lam + μ * lam| * |Work.Spaces.Dz g z θ| := by
          rw [abs_mul, abs_neg, abs_mul]
  simp only [Work.Construction.Nstar]
  linarith

end Work.FTS.StrongEps.gRHSBound
