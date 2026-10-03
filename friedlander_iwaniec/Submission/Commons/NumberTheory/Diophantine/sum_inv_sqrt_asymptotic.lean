import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Commons.Analysis.Sum.sum_inv_sqrt_le

namespace Commons.NumberTheory.Diophantine

/-- Pointwise lower-bound ingredient: for `x ≥ 1`,
`2(√(x+1) - √x) ≤ (√x)⁻¹`. -/
private lemma sqrt_step_le_inv_sqrt (x : ℝ) (hx : 1 ≤ x) :
    2 * (Real.sqrt (x + 1) - Real.sqrt x) ≤ (Real.sqrt x)⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hxn : 0 ≤ x := le_of_lt hx0
  have hx1 : 0 ≤ x + 1 := by linarith
  have ha : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx0
  have hb : 0 < Real.sqrt (x + 1) := Real.sqrt_pos_of_pos (by linarith)
  have hd : 0 < Real.sqrt (x + 1) + Real.sqrt x := by linarith
  have hsq_a : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hxn
  have hsq_b : (Real.sqrt (x + 1)) ^ 2 = x + 1 := Real.sq_sqrt hx1
  have hsub : Real.sqrt (x + 1) - Real.sqrt x
      = 1 / (Real.sqrt (x + 1) + Real.sqrt x) := by
    rw [eq_div_iff (ne_of_gt hd)]
    nlinarith [hsq_a, hsq_b]
  have hle : Real.sqrt x ≤ Real.sqrt (x + 1) := Real.sqrt_le_sqrt (by linarith)
  rw [hsub, mul_one_div, inv_eq_one_div]
  rw [div_le_div_iff₀ hd ha]
  linarith

/-- Lower bound on the partial sums of `1/√n`: for every `D`,
`2√(D+1) - 2 ≤ ∑_{d=1}^{D} 1/√d`. -/
private lemma sum_inv_sqrt_ge' (D : ℕ) :
    2 * Real.sqrt ((D : ℝ) + 1) - 2
      ≤ ∑ d ∈ Finset.Icc 1 D, (Real.sqrt (d : ℝ))⁻¹ := by
  induction D with
  | zero =>
      rw [Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0)]
      norm_num
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      push_cast
      have hpt : 2 * (Real.sqrt ((n : ℝ) + 1 + 1) - Real.sqrt ((n : ℝ) + 1))
          ≤ (Real.sqrt ((n : ℝ) + 1))⁻¹ :=
        sqrt_step_le_inv_sqrt ((n : ℝ) + 1) (by linarith)
      linarith [ih, hpt]

theorem sum_inv_sqrt_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
      |(∑ n ∈ Finset.Icc 1 x, (Real.sqrt (n : ℝ))⁻¹) - 2 * Real.sqrt x| ≤ C := by
  refine ⟨2, by norm_num, ?_⟩
  intro x _hx
  have hub : (∑ n ∈ Finset.Icc 1 x, (Real.sqrt (n : ℝ))⁻¹) ≤ 2 * Real.sqrt (x : ℝ) :=
    Commons.Analysis.Sum.sum_inv_sqrt_le x
  have hlb : 2 * Real.sqrt ((x : ℝ) + 1) - 2
      ≤ ∑ n ∈ Finset.Icc 1 x, (Real.sqrt (n : ℝ))⁻¹ :=
    sum_inv_sqrt_ge' x
  have hmono : Real.sqrt (x : ℝ) ≤ Real.sqrt ((x : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  rw [abs_le]
  constructor <;> linarith

end Commons.NumberTheory.Diophantine