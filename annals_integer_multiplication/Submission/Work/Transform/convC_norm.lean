import Mathlib
import Submission.Work.Transform.Defs

namespace Work.Transform

open scoped BigOperators

/-- Reading a vector at a natural index never exceeds the sup norm (the index is either in
range, in which case it is an entry of the vector, or out of range, in which case the value
is `0`). -/
private lemma vget_norm_le {n : ℕ} (w : Fin n → ℂ) (i : ℕ) : ‖HvdH.vget w i‖ ≤ ‖w‖ := by
  by_cases h : i < n
  · rw [HvdH.vget, dite_eq_left h]
    exact norm_le_pi_norm w ⟨i, h⟩
  · rw [HvdH.vget, dite_eq_right h]
    simp

/-- The normalised complex convolution is a contraction: `‖M_C(u,v)‖ ≤ ‖u‖‖v‖`. -/
theorem convC_norm (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (u v : Fin ts.prod → ℂ) :
    ‖HvdH.convC ts u v‖ ≤ ‖u‖ * ‖v‖ := by
  have hTpos : 0 < ts.prod := List.prod_pos hpos
  have hnn : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg hnn).2 (fun j => ?_)
  rw [HvdH.convC]
  have hnorm_inv : ‖(1 / (ts.prod : ℂ))‖ = (ts.prod : ℝ)⁻¹ := by
    rw [one_div, norm_inv, Complex.norm_natCast]
  -- every summand has norm at most `‖u‖ * ‖v‖`, and there are `ts.prod` of them
  have hS : ‖∑ k : Fin ts.prod, u k * HvdH.vget v (HvdH.subIdx ts (j : ℕ) (k : ℕ))‖
      ≤ (ts.prod : ℝ) * (‖u‖ * ‖v‖) := by
    calc _ ≤ ∑ k : Fin ts.prod, ‖u k * HvdH.vget v (HvdH.subIdx ts (j : ℕ) (k : ℕ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Fin ts.prod, ‖u‖ * ‖v‖ := by
          apply Finset.sum_le_sum
          intro k _
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm u k) (vget_norm_le v _)
            (norm_nonneg _) (norm_nonneg _)
      _ = (ts.prod : ℝ) * (‖u‖ * ‖v‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the normalising factor `1/T` (paper: `M_C` is `1/T` times the cyclic sum)
  calc ‖(1 / (ts.prod : ℂ)) * ∑ k : Fin ts.prod,
        u k * HvdH.vget v (HvdH.subIdx ts (j : ℕ) (k : ℕ))‖
      = ‖(1 / (ts.prod : ℂ))‖ * ‖∑ k : Fin ts.prod,
        u k * HvdH.vget v (HvdH.subIdx ts (j : ℕ) (k : ℕ))‖ := norm_mul _ _
    _ = (ts.prod : ℝ)⁻¹ * ‖∑ k : Fin ts.prod,
        u k * HvdH.vget v (HvdH.subIdx ts (j : ℕ) (k : ℕ))‖ := by rw [hnorm_inv]
    _ ≤ (ts.prod : ℝ)⁻¹ * ((ts.prod : ℝ) * (‖u‖ * ‖v‖)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = ‖u‖ * ‖v‖ := by
        have hne : (ts.prod : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hTpos)
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Work.Transform
