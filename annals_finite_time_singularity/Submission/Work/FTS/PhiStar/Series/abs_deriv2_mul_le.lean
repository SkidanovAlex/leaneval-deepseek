import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series

lemma abs_deriv2_mul_le {f g : ℝ → ℝ} {θ : ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hf' : DifferentiableAt ℝ (deriv f) θ) (hg' : DifferentiableAt ℝ (deriv g) θ)
    {A B A' B' : ℝ} (hA : |deriv f θ| ≤ A) (hB : |deriv g θ| ≤ B)
    (hA' : |deriv (deriv f) θ| ≤ A') (hB' : |deriv (deriv g) θ| ≤ B')
    (hf0 : 0 ≤ f θ) (hf1 : f θ ≤ 1) (hg0 : 0 ≤ g θ) (hg1 : g θ ≤ 1) :
    |deriv (deriv (f * g)) θ| ≤ A' + 2 * A * B + B' := by
  -- Leibniz twice: `(f * g)'' = f'' * g + 2 * (f' * g') + f * g''`.
  have hderiv : deriv (deriv (f * g)) θ
      = deriv (deriv f) θ * g θ + 2 * (deriv f θ * deriv g θ) + f θ * deriv (deriv g) θ := by
    have h1 : deriv (f * g) = fun x => deriv f x * g x + f x * deriv g x := by
      funext x
      exact deriv_mul (hf x) (hg x)
    rw [h1]
    have hd1 : DifferentiableAt ℝ (fun x => deriv f x * g x) θ := hf'.mul hg.differentiableAt
    have hd2 : DifferentiableAt ℝ (fun x => f x * deriv g x) θ := hf.differentiableAt.mul hg'
    change deriv ((fun x => deriv f x * g x) + (fun x => f x * deriv g x)) θ = _
    rw [deriv_add hd1 hd2]
    change deriv ((deriv f) * g) θ + deriv (f * deriv g) θ = _
    rw [deriv_mul hf' hg.differentiableAt, deriv_mul hf.differentiableAt hg']
    ring
  rw [hderiv]
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) hA
  have hA'0 : 0 ≤ A' := le_trans (abs_nonneg _) hA'
  have hgn : |g θ| ≤ 1 := abs_le.2 ⟨by linarith [hg0], hg1⟩
  have hfn : |f θ| ≤ 1 := abs_le.2 ⟨by linarith [hf0], hf1⟩
  have h1 : |deriv (deriv f) θ * g θ| ≤ A' := by
    rw [abs_mul]
    calc |deriv (deriv f) θ| * |g θ| ≤ A' * 1 := mul_le_mul hA' hgn (abs_nonneg _) hA'0
      _ = A' := mul_one A'
  have h2 : |2 * (deriv f θ * deriv g θ)| ≤ 2 * A * B := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul]
    calc 2 * (|deriv f θ| * |deriv g θ|) ≤ 2 * (A * B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hA hB (abs_nonneg _) hA0) (by norm_num)
      _ = 2 * A * B := by ring
  have h3 : |f θ * deriv (deriv g) θ| ≤ B' := by
    rw [abs_mul]
    calc |f θ| * |deriv (deriv g) θ| ≤ 1 * B' :=
          mul_le_mul hfn hB' (abs_nonneg _) (by norm_num)
      _ = B' := one_mul B'
  calc |deriv (deriv f) θ * g θ + 2 * (deriv f θ * deriv g θ) + f θ * deriv (deriv g) θ|
      ≤ |deriv (deriv f) θ * g θ + 2 * (deriv f θ * deriv g θ)| + |f θ * deriv (deriv g) θ| :=
        abs_add_le _ _
    _ ≤ (|deriv (deriv f) θ * g θ| + |2 * (deriv f θ * deriv g θ)|)
          + |f θ * deriv (deriv g) θ| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ A' + 2 * A * B + B' := by linarith

end Work.FTS.PhiStar.Series
