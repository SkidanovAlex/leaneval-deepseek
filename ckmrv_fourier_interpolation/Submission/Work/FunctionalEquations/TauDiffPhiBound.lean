import Mathlib
import Submission.Work.FunctionalEquations.TauDiffSetup

namespace Work.FunctionalEquations

theorem TauDiffPhiBound (c : ℕ → ℂ) {α β : ℝ}
    (hbound : ∀ (k : ℕ) (y : ℝ), 0 < y →
      ‖c k‖ ≤ 2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y))
    {y : ℝ} (hy : 0 < y) :
    Work.FunctionalEquations.dirichletNormSum c y ≤ 2 * α * (y / 2) ^ (-β) *
      (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))) := by
  set B : ℝ := 2 * α * (y / 2) ^ (-β) with hB
  set r : ℝ := Real.exp (-(Real.pi * y)) with hr
  have hrpos : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hrlt1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hy]
  have hrn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hrpos]; exact hrlt1
  have hgeom1 : Summable (fun k : ℕ => r ^ (k+1)) := by
    simpa only [pow_succ'] using (summable_geometric_of_norm_lt_one hrn).mul_left r
  have hf : Summable (fun k : ℕ => B * r ^ (k+1)) := hgeom1.mul_left B
  have hterm : ∀ k : ℕ,
      ‖c k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y)) ≤ B * r ^ (k+1) := by
    intro k
    have hb := hbound k y hy
    have h2 : (0:ℝ) ≤ Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y)) :=
      le_of_lt (Real.exp_pos _)
    calc ‖c k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y))
        ≤ (B * Real.exp (Real.pi * ((k : ℝ) + 1) * y))
            * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y)) :=
          mul_le_mul_of_nonneg_right hb h2
      _ = B * (Real.exp (Real.pi * ((k : ℝ) + 1) * y)
            * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y))) := by ring_nf
      _ = B * Real.exp (-(Real.pi * ((k : ℝ) + 1) * y)) := by
          rw [← Real.exp_add]; congr 1; ring_nf
      _ = B * r ^ (k+1) := by
          rw [hr, ← Real.exp_nat_mul]; congr 1; push_cast; ring_nf
  have hgs : Summable (fun k : ℕ => ‖c k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y))) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (le_of_lt (Real.exp_pos _)))
      hterm hf
  have hle : dirichletNormSum c y ≤ ∑' k : ℕ, B * r ^ (k+1) := by
    rw [dirichletNormSum]
    exact Summable.tsum_le_tsum hterm hgs hf
  have h1 : (∑' k : ℕ, r ^ (k+1)) = r * (∑' k : ℕ, r ^ k) := by
    rw [show (fun k : ℕ => r ^ (k+1)) = (fun k : ℕ => r * r ^ k) from by
      funext k; rw [pow_succ']]
    exact tsum_mul_left
  calc dirichletNormSum c y ≤ ∑' k : ℕ, B * r ^ (k+1) := hle
    _ = B * (r / (1 - r)) := by
        rw [tsum_mul_left, h1, tsum_geometric_of_norm_lt_one hrn, div_eq_mul_inv]

end Work.FunctionalEquations
