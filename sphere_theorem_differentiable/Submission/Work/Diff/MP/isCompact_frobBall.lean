import Mathlib
import Submission.Work.Diff.MP.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.MP

open Submission.Diff.Alg
open Work.Diff.MP

/-!
# Compactness of the Frobenius ball and the Frobenius unit sphere in `Curv4 n`

`Curv4 n = Fin n → Fin n → Fin n → Fin n → ℝ` is a finite-dimensional real normed space
(equipped with the sup norm), hence a proper metric space.  The Frobenius norm
`frobNorm R = √(frobDot R R)` is continuous, so the Frobenius ball `frobBall ρ = {R | frobNorm R ≤ ρ}`
is closed, and the Frobenius unit sphere `{u | frobNorm u = 1}` is closed.  Both are bounded (each
coordinate `R i j k l` satisfies `|R i j k l| ≤ frobNorm R`, so the sup norm is controlled by `ρ`,
resp. by `1`).  Heine–Borel in the proper space `Curv4 n` then gives compactness.

The main ingredient is the coordinate bound `abs_apply_le_frobNorm`: the Frobenius norm dominates
every coordinate, because `frobDot R R` is a sum of squares.
-/

/-- Every coordinate of a curvature array is bounded in absolute value by its Frobenius norm:
`frobDot R R` is the sum of the squares `R i j k l ^ 2`, hence dominates each single term. -/
theorem abs_apply_le_frobNorm {n : ℕ} (R : Curv4 n) (i j k l : Fin n) :
    |R i j k l| ≤ frobNorm R := by
  rw [frobNorm]
  apply Real.abs_le_sqrt
  rw [pow_two]
  simp only [frobDot]
  calc R i j k l * R i j k l
      ≤ ∑ l', R i j k l' * R i j k l' :=
        Finset.single_le_sum (fun _ _ => mul_self_nonneg _) (Finset.mem_univ l)
    _ ≤ ∑ k', ∑ l', R i j k' l' * R i j k' l' :=
        Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
          (Finset.mem_univ k)
    _ ≤ ∑ j', ∑ k', ∑ l', R i j' k' l' * R i j' k' l' :=
        Finset.single_le_sum
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ∑ k', ∑ l', R i' j' k' l' * R i' j' k' l' :=
        Finset.single_le_sum
          (fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
          (Finset.mem_univ i)

theorem isCompact_frobBall (n : ℕ) (ρ : ℝ) :
    IsCompact (frobBall (n := n) ρ) ∧ IsCompact {u : Curv4 n | frobNorm u = 1} := by
  -- `frobNorm` is continuous (a square root of a polynomial in the coordinates).
  have hcont : Continuous fun R : Curv4 n => frobNorm R := by
    simp only [frobNorm, frobDot]; fun_prop
  -- closedness
  have hcl : IsClosed (frobBall (n := n) ρ) := by
    rw [frobBall]
    exact IsClosed.preimage hcont isClosed_Iic
  have hcl2 : IsClosed {u : Curv4 n | frobNorm u = 1} := by
    rw [show {u : Curv4 n | frobNorm u = 1} = frobNorm ⁻¹' ({1} : Set ℝ) by
          ext u; simp]
    exact IsClosed.preimage hcont isClosed_singleton
  -- boundedness: the sup norm is dominated by the Frobenius norm coordinatewise
  have hbd : Bornology.IsBounded (frobBall (n := n) ρ) :=
    (Metric.isBounded_closedBall (x := (0 : Curv4 n)) (r := max ρ 0)).subset (by
      intro R hR
      change frobNorm R ≤ ρ at hR
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg (le_max_right ρ 0)]
      intro i
      rw [pi_norm_le_iff_of_nonneg (le_max_right ρ 0)]
      intro j
      rw [pi_norm_le_iff_of_nonneg (le_max_right ρ 0)]
      intro k
      rw [pi_norm_le_iff_of_nonneg (le_max_right ρ 0)]
      intro l
      rw [Real.norm_eq_abs]
      exact le_trans (abs_apply_le_frobNorm R i j k l) (le_trans hR (le_max_left ρ 0)))
  have hbd2 : Bornology.IsBounded {u : Curv4 n | frobNorm u = 1} :=
    (Metric.isBounded_closedBall (x := (0 : Curv4 n)) (r := 1)).subset (by
      intro u hu
      change frobNorm u = 1 at hu
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro j
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro k
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro l
      rw [Real.norm_eq_abs]
      exact le_trans (abs_apply_le_frobNorm u i j k l) (le_of_eq hu))
  -- Heine–Borel in the proper space `Curv4 n`
  exact ⟨Metric.isCompact_iff_isClosed_bounded.mpr ⟨hcl, hbd⟩,
         Metric.isCompact_iff_isClosed_bounded.mpr ⟨hcl2, hbd2⟩⟩

end Work.Diff.MP
