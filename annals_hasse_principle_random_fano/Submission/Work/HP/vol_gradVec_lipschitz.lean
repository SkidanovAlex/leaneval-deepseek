import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.evaldefs
import Submission.Work.HP.veronese_first

/-!
# `Work.HP.vol_gradVec_lipschitz`

Lipschitz bound for the gradient map `a ↦ x ↦ ∇f_a(x)` on the Euclidean ball of radius `2`,
with the explicit constant `(n+1) · N_{d,n} · 2^{3d}`.

The proof is a direct `ℓ¹` estimate: the `j`-th coordinate of `∇f_a(y) - ∇f_a(x)` is
`∑_m a_m (∂_j x^m(y) - ∂_j x^m(x))`, each summand of which is bounded by
`|a_m| · 2^{3d} ‖y - x‖` (the Lipschitz bound `vf_dm_lip` for the partial derivatives of the
monomials, proved in `Submission/Work/HP/veronese_first.lean`).  Summing over the `n+1`
coordinates and using `∑_m |a_m| ≤ N_{d,n} ‖a‖` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators

namespace Work.HP

/-- `∑_m |a m| ≤ N_{d,n} · ‖a‖`: the `ℓ¹` norm of the coefficient vector is at most the
number of monomials times the Euclidean norm. -/
lemma sum_abs_coeff_le (d n : ℕ) (a : Mon d n → ℝ) :
    (∑ m : Mon d n, |a m|) ≤ (NN d n : ℝ) * rNorm a := by
  calc (∑ m : Mon d n, |a m|) ≤ ∑ _m : Mon d n, rNorm a :=
        Finset.sum_le_sum (fun m _ => abs_coeff_le_rNorm a m)
    _ = (NN d n : ℝ) * rNorm a := by
        simp [NN, Finset.sum_const, nsmul_eq_mul]

/-- On the ball of radius `2`, the gradient map `x ↦ ∇f_a(x)` is Lipschitz with constant
`(n+1) · N_{d,n} · 2^{3d} · ‖a‖`. -/
theorem vol_gradVec_lipschitz (d n : ℕ) (a : Work.HP.Mon d n → ℝ) (x y : Fin (n + 1) → ℝ)
    (hx : Work.HP.rNorm x ≤ 2) (hy : Work.HP.rNorm y ≤ 2) :
    Work.HP.rNorm (Work.HP.gradVec d n a y - Work.HP.gradVec d n a x)
      ≤ ((n + 1 : ℝ) * (Work.HP.NN d n : ℝ) * (2 : ℝ) ^ (3 * d)) * Work.HP.rNorm a *
          Work.HP.rNorm (y - x) := by
  have hε : 0 ≤ rNorm (y - x) := rNorm_nonneg _
  have hc : 0 ≤ (2 : ℝ) ^ (3 * d) * rNorm (y - x) :=
    mul_nonneg (by positivity) hε
  -- coordinate-wise bound
  have hL : ∀ j : Fin (n + 1),
      |gradVec d n a y j - gradVec d n a x j|
        ≤ (∑ m : Mon d n, |a m|) * ((2 : ℝ) ^ (3 * d) * rNorm (y - x)) := by
    intro j
    simp only [gradVec_eq_sum_dm]
    have hdiff : (∑ m : Mon d n, a m * dm d n m y j) - (∑ m : Mon d n, a m * dm d n m x j)
        = ∑ m : Mon d n, a m * (dm d n m y j - dm d n m x j) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hdiff]
    calc |∑ m : Mon d n, a m * (dm d n m y j - dm d n m x j)|
        ≤ ∑ m : Mon d n, |a m * (dm d n m y j - dm d n m x j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m : Mon d n, |a m| * ((2 : ℝ) ^ (3 * d) * rNorm (y - x)) := by
            refine Finset.sum_le_sum (fun m _ => ?_)
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (vf_dm_lip d n m x y j hx hy) (abs_nonneg _)
      _ = (∑ m : Mon d n, |a m|) * ((2 : ℝ) ^ (3 * d) * rNorm (y - x)) := by
            rw [Finset.sum_mul]
  calc rNorm (gradVec d n a y - gradVec d n a x)
      ≤ ∑ j : Fin (n + 1), |gradVec d n a y j - gradVec d n a x j| := by
        simpa using rNorm_le_sum_abs (gradVec d n a y - gradVec d n a x)
    _ ≤ ∑ _j : Fin (n + 1),
          (∑ m : Mon d n, |a m|) * ((2 : ℝ) ^ (3 * d) * rNorm (y - x)) :=
        Finset.sum_le_sum (fun j _ => hL j)
    _ = (n + 1 : ℝ) * ((∑ m : Mon d n, |a m|) * ((2 : ℝ) ^ (3 * d) * rNorm (y - x))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n + 1 : ℝ) *
          (((NN d n : ℝ) * rNorm a) * ((2 : ℝ) ^ (3 * d) * rNorm (y - x))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (sum_abs_coeff_le d n a) hc
    _ = ((n + 1 : ℝ) * (NN d n : ℝ) * (2 : ℝ) ^ (3 * d)) * rNorm a * rNorm (y - x) := by
        ring

end Work.HP
