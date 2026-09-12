import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.InnerProductSpace

open scoped BigOperators

theorem compl_norm_sq_eq {n : ℕ} [NeZero n] (y : EuclideanSpace ℝ (Fin n)) :
    ‖y - (y (0 : Fin n)) • EuclideanSpace.single (0 : Fin n) (1 : ℝ)‖ ^ 2 =
      ∑ i : Fin n, (if i = (0 : Fin n) then 0 else (y i) ^ 2) := by
  have hcoord : ∀ i : Fin n,
      ‖(y - (y (0 : Fin n)) • EuclideanSpace.single (0 : Fin n) (1 : ℝ)).ofLp i‖ ^ 2 =
        (if i = (0 : Fin n) then 0 else (y i) ^ 2) := by
    intro i
    have hc : (y - (y (0 : Fin n)) • EuclideanSpace.single (0 : Fin n) (1 : ℝ)).ofLp i =
        (if i = (0 : Fin n) then 0 else y i) := by
      by_cases h : i = 0
      · subst h; simp
      · simp [h]
    rw [hc]
    by_cases h : i = 0
    · subst h; simp
    · simp [h, Real.norm_eq_abs, sq_abs]
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl (fun i _ => hcoord i)

end Commons.Analysis.InnerProductSpace