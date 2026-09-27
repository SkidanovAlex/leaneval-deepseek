import Mathlib

namespace Work.EKLC7

open Matrix Finset in
/-- Entrywise bound for a product of three real matrices.

If every entry of `W` is bounded by `C`, then every entry of `U * W * V` is bounded by
`C` times the "total mass" `∑ a, ∑ b, |U a b|` of `U` times the total mass of `V`. -/
lemma abs_mul_entry_le {n : Type*} [Fintype n] [Nonempty n]
    (U W V : Matrix n n ℝ) (C : ℝ) (hC : ∀ a b, |W a b| ≤ C) (i j : n) :
    |(U * W * V) i j| ≤ C * (∑ a, ∑ b, |U a b|) * (∑ a, ∑ b, |V a b|) := by
  have hC0 : 0 ≤ C :=
    le_trans (abs_nonneg _) (hC (Classical.arbitrary n) (Classical.arbitrary n))
  have step1 : |(U * W * V) i j| ≤ ∑ b, |(U * W) i b| * |V b j| := by
    calc |(U * W * V) i j| = |∑ b, (U * W) i b * V b j| := by rw [Matrix.mul_apply]
      _ ≤ ∑ b, |(U * W) i b * V b j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ b, |(U * W) i b| * |V b j| := by simp only [abs_mul]
  have step2 : ∀ b, |(U * W) i b| ≤ C * (∑ a, |U i a|) := by
    intro b
    calc |(U * W) i b| = |∑ a, U i a * W a b| := by rw [Matrix.mul_apply]
      _ ≤ ∑ a, |U i a * W a b| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a, |U i a| * |W a b| := by simp only [abs_mul]
      _ ≤ ∑ a, |U i a| * C :=
          Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hC a b) (abs_nonneg _))
      _ = (∑ a, |U i a|) * C := by rw [Finset.sum_mul]
      _ = C * (∑ a, |U i a|) := by ring
  have step3 : |(U * W * V) i j| ≤ C * (∑ a, |U i a|) * (∑ b, |V b j|) := by
    calc |(U * W * V) i j| ≤ ∑ b, |(U * W) i b| * |V b j| := step1
      _ ≤ ∑ b, (C * (∑ a, |U i a|)) * |V b j| :=
          Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right (step2 b) (abs_nonneg _))
      _ = C * (∑ a, |U i a|) * (∑ b, |V b j|) :=
          (Finset.mul_sum Finset.univ (fun b => |V b j|) (C * (∑ a, |U i a|))).symm
  have hrow : ∑ a, |U i a| ≤ ∑ a, ∑ b, |U a b| :=
    Finset.single_le_sum (f := fun a' => ∑ b, |U a' b|)
      (fun a' _ => Finset.sum_nonneg (fun b _ => abs_nonneg _)) (Finset.mem_univ i)
  have hcol : ∑ b, |V b j| ≤ ∑ a, ∑ b, |V a b| := by
    apply Finset.sum_le_sum
    intro b _
    exact Finset.single_le_sum (f := fun a => |V b a|) (fun a _ => abs_nonneg _) (Finset.mem_univ j)
  have hrow0 : 0 ≤ ∑ a, |U i a| := Finset.sum_nonneg (fun a _ => abs_nonneg _)
  have hcol0 : 0 ≤ ∑ b, |V b j| := Finset.sum_nonneg (fun b _ => abs_nonneg _)
  have hSU0 : 0 ≤ ∑ a, ∑ b, |U a b| :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg _))
  refine le_trans step3 ?_
  have h1 : C * (∑ a, |U i a|) ≤ C * (∑ a, ∑ b, |U a b|) :=
    mul_le_mul_of_nonneg_left hrow hC0
  have h2 : C * (∑ a, ∑ b, |U a b|) * (∑ b, |V b j|)
      ≤ C * (∑ a, ∑ b, |U a b|) * (∑ a, ∑ b, |V a b|) :=
    mul_le_mul_of_nonneg_left hcol (mul_nonneg hC0 hSU0)
  exact le_trans (mul_le_mul_of_nonneg_right h1 hcol0) h2

theorem conj_entry_bound {u w : Matrix.SpecialLinearGroup (Fin 3) ℝ} (C : ℝ)
    (hC : ∀ i j : Fin 3, |w i j| ≤ C) (i j : Fin 3) :
    |(u * w * u⁻¹) i j| ≤
      C * (∑ a : Fin 3, ∑ b : Fin 3, |u a b|) * (∑ a : Fin 3, ∑ b : Fin 3, |u⁻¹ a b|) := by
  have hcoe : ((u * w * u⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
      = (u : Matrix (Fin 3) (Fin 3) ℝ) * (w : Matrix (Fin 3) (Fin 3) ℝ)
        * ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have key := abs_mul_entry_le (u : Matrix (Fin 3) (Fin 3) ℝ) (w : Matrix (Fin 3) (Fin 3) ℝ)
    ((u⁻¹ : Matrix.SpecialLinearGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) C hC i j
  rw [← hcoe] at key
  exact key

end Work.EKLC7
