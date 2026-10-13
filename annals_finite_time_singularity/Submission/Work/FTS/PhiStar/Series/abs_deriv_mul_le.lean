import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.RCLike.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

lemma abs_deriv_mul_le {f g : ℝ → ℝ} {θ : ℝ} (hf : DifferentiableAt ℝ f θ)
    (hg : DifferentiableAt ℝ g θ) {A B : ℝ} (hA : |deriv f θ| ≤ A) (hB : |deriv g θ| ≤ B)
    (hf0 : 0 ≤ f θ) (hf1 : f θ ≤ 1) (hg0 : 0 ≤ g θ) (hg1 : g θ ≤ 1) :
    |deriv (f * g) θ| ≤ A + B := by
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) hA
  have hgabs : |g θ| ≤ 1 := abs_le.2 ⟨by linarith, hg1⟩
  have hfabs : |f θ| ≤ 1 := abs_le.2 ⟨by linarith, hf1⟩
  have h1 : |deriv f θ * g θ| ≤ A := by
    rw [abs_mul]
    calc |deriv f θ| * |g θ| ≤ A * 1 :=
          mul_le_mul hA hgabs (abs_nonneg _) hA0
      _ = A := mul_one A
  have h2 : |f θ * deriv g θ| ≤ B := by
    rw [abs_mul]
    calc |f θ| * |deriv g θ| ≤ 1 * B :=
          mul_le_mul hfabs hB (abs_nonneg _) (by norm_num)
      _ = B := one_mul B
  rw [deriv_mul hf hg]
  calc |deriv f θ * g θ + f θ * deriv g θ|
      ≤ |deriv f θ * g θ| + |f θ * deriv g θ| := abs_add_le _ _
    _ ≤ A + B := add_le_add h1 h2

end Work.FTS.PhiStar.Series
