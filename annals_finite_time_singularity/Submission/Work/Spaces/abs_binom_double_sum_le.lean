import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith.Frontend

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

theorem abs_binom_double_sum_le (k j : ℕ) (x y : ℕ → ℕ → ℝ) :
    |∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (k + 1),
        (j.choose a : ℝ) * (k.choose c : ℝ) * (x a c * y a c)| ≤
      (1 + ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (k + 1),
        (j.choose a : ℝ) * (k.choose c : ℝ)) *
        ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1), |x a c| * |y a c| := by
  set sA : Finset ℕ := Finset.range (j + 1) with hsA
  set sC : Finset ℕ := Finset.range (k + 1) with hsC
  set S : ℝ := ∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) with hS
  set T : ℝ := ∑ c ∈ sC, ∑ a ∈ sA, |x a c| * |y a c| with hT
  have hBnn : ∀ a c, (0 : ℝ) ≤ (j.choose a : ℝ) * (k.choose c : ℝ) :=
    fun a c => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hznn : ∀ a c, (0 : ℝ) ≤ |x a c| * |y a c| :=
    fun a c => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  -- Step 1: triangle inequality, and `|B * (x*y)| = B * |x| * |y|` since `B ≥ 0`.
  have step1 :
      |∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (x a c * y a c)|
      ≤ ∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (|x a c| * |y a c|) := by
    calc
      |∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (x a c * y a c)|
          ≤ ∑ a ∈ sA, |∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (x a c * y a c)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ sA, ∑ c ∈ sC, |(j.choose a : ℝ) * (k.choose c : ℝ) * (x a c * y a c)| :=
            Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (|x a c| * |y a c|) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro c _
            rw [abs_mul, abs_of_nonneg (hBnn a c), abs_mul]
  -- Each `B a c` is bounded by the full double sum `S`.
  have hB_le : ∀ a ∈ sA, ∀ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) ≤ 1 + S := by
    intro a ha c hc
    have h2 : (j.choose a : ℝ) * (k.choose c : ℝ)
        ≤ ∑ c' ∈ sC, (j.choose a : ℝ) * (k.choose c' : ℝ) :=
      Finset.single_le_sum (fun c' _ => hBnn a c') hc
    have h1 : (∑ c' ∈ sC, (j.choose a : ℝ) * (k.choose c' : ℝ)) ≤ S := by
      rw [hS]
      exact Finset.single_le_sum (fun a' _ => Finset.sum_nonneg (fun c' _ => hBnn a' c')) ha
    have hBS : (j.choose a : ℝ) * (k.choose c : ℝ) ≤ S := h2.trans h1
    linarith
  -- Step 2: bound termwise by `(1+S) * z`, then factor `(1+S)` out.
  have step2 :
      (∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (|x a c| * |y a c|))
      ≤ (1 + S) * T := by
    have hstep : ∑ a ∈ sA, ∑ c ∈ sC, (j.choose a : ℝ) * (k.choose c : ℝ) * (|x a c| * |y a c|)
        ≤ ∑ a ∈ sA, ∑ c ∈ sC, (1 + S) * (|x a c| * |y a c|) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_right (hB_le a ha c hc) (hznn a c)
    refine hstep.trans (le_of_eq ?_)
    have heq : (∑ a ∈ sA, ∑ c ∈ sC, (1 + S) * (|x a c| * |y a c|)) = (1 + S) * T := by
      rw [hT, Finset.sum_comm (s := sA) (t := sC)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
    exact heq
  exact step1.trans step2

end Work.Spaces
