import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Int.Star
import Submission.Work.FTS.PhiStar.FamLopAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

open Finset

/-- `famC k = 0` for `k < 0`: the coefficient sequence is extended by `0` to the
negative integers. -/
private lemma famC_eq_zero_of_neg {k : ℤ} (hk : k < 0) : Work.FTS.PhiStar.famC k = 0 := by
  rw [Work.FTS.PhiStar.famC]
  split_ifs with h
  · exact absurd h (by omega)
  · rfl

/-- The `j`-th summand of `famTrig n ψ`. -/
private noncomputable def famBase (n : ℕ) (ψ : ℝ) (j : ℕ) : ℝ :=
  Work.FTS.PhiStar.famC (j : ℤ) * Work.FTS.PhiStar.famC ((n : ℤ) - (j : ℤ))
    * Real.cos ((2 * (j : ℝ) - (n : ℝ)) * ψ)

/-- The `j`-th summand of the `(n+3)`-term sum of `famTrig_shift`. -/
private noncomputable def famShift (n : ℕ) (ψ : ℝ) (j : ℕ) : ℝ :=
  Work.FTS.PhiStar.famC ((j : ℤ) - 1) * Work.FTS.PhiStar.famC ((n : ℤ) + 1 - (j : ℤ))
    * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ)

private lemma famShift_zero (n : ℕ) (ψ : ℝ) : famShift n ψ 0 = 0 := by
  have h : ((0 : ℕ) : ℤ) - 1 = (-1 : ℤ) := by norm_num
  simp only [famShift, h, famC_eq_zero_of_neg (show (-1 : ℤ) < 0 by norm_num), zero_mul]

private lemma famShift_last (n : ℕ) (ψ : ℝ) : famShift n ψ (n + 2) = 0 := by
  have h : (n : ℤ) + 1 - (((n + 2 : ℕ)) : ℤ) = (-1 : ℤ) := by push_cast; ring
  simp only [famShift, h, famC_eq_zero_of_neg (show (-1 : ℤ) < 0 by norm_num), zero_mul,
    mul_zero]

private lemma famShift_succ (n : ℕ) (ψ : ℝ) (j : ℕ) :
    famShift n ψ (j + 1) = famBase n ψ j := by
  have h1 : (((j + 1 : ℕ)) : ℤ) - 1 = (j : ℤ) := by push_cast; ring
  have h2 : (n : ℤ) + 1 - (((j + 1 : ℕ)) : ℤ) = (n : ℤ) - (j : ℤ) := by push_cast; ring
  have h3 : (2 * (((j + 1 : ℕ)) : ℝ) - ((n : ℝ) + 2)) = (2 * (j : ℝ) - (n : ℝ)) := by
    push_cast; ring
  simp only [famShift, famBase, h1, h2, h3]

/-- Shifting a summation range: if `f 0 = 0` then `∑_{j<N} f (j+1) = ∑_{i<N+1} f i`. -/
private lemma shift_one (f : ℕ → ℝ) (hf : f 0 = 0) (N : ℕ) :
    (∑ j ∈ Finset.range N, f (j + 1)) = ∑ i ∈ Finset.range (N + 1), f i := by
  rw [Finset.sum_range_succ' f N, hf, add_zero]

private lemma famShift_sum (n : ℕ) (ψ : ℝ) :
    (∑ j ∈ Finset.range (n + 3), famShift n ψ j)
      = ∑ j ∈ Finset.range (n + 1), famBase n ψ j := by
  have h1 : (∑ j ∈ Finset.range (n + 3), famShift n ψ j)
      = (∑ j ∈ Finset.range (n + 2), famShift n ψ j) + famShift n ψ (n + 2) := by
    have hn : n + 3 = (n + 2) + 1 := by omega
    rw [hn]
    exact Finset.sum_range_succ (famShift n ψ) (n + 2)
  have h3 : (∑ j ∈ Finset.range (n + 2), famShift n ψ j)
      = ∑ j ∈ Finset.range (n + 1), famShift n ψ (j + 1) :=
    (shift_one (famShift n ψ) (famShift_zero n ψ) (n + 1)).symm
  calc (∑ j ∈ Finset.range (n + 3), famShift n ψ j)
      = (∑ j ∈ Finset.range (n + 2), famShift n ψ j) + famShift n ψ (n + 2) := h1
    _ = ∑ j ∈ Finset.range (n + 2), famShift n ψ j := by
        rw [famShift_last n ψ, add_zero]
    _ = ∑ j ∈ Finset.range (n + 1), famShift n ψ (j + 1) := h3
    _ = ∑ j ∈ Finset.range (n + 1), famBase n ψ j :=
        Finset.sum_congr rfl (fun j _ => famShift_succ n ψ j)

theorem famTrig_shift (n : ℕ) (ψ : ℝ) :
    Work.FTS.PhiStar.famTrig n ψ
      = ∑ j ∈ Finset.range (n + 3),
          Work.FTS.PhiStar.famC ((j : ℤ) - 1) * Work.FTS.PhiStar.famC ((n : ℤ) + 1 - (j : ℤ))
            * Real.cos ((2 * (j : ℝ) - ((n : ℝ) + 2)) * ψ) := by
  rw [Work.FTS.PhiStar.famTrig]
  change (∑ j ∈ Finset.range (n + 1), famBase n ψ j)
    = ∑ j ∈ Finset.range (n + 3), famShift n ψ j
  exact (famShift_sum n ψ).symm

end Work.FTS.PhiStar.FlatWAux
