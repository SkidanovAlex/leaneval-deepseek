import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.InnerProductSpace

open scoped BigOperators

theorem erase_sum_sq_eq_if {n : ℕ} [NeZero n] (y : EuclideanSpace ℝ (Fin n)) :
    (∑ i ∈ (Finset.univ : Finset (Fin n)).erase (0 : Fin n), (y i) ^ 2) =
      ∑ i : Fin n, (if i = (0 : Fin n) then 0 else (y i) ^ 2) := by
  classical
  calc
    (∑ i ∈ (Finset.univ : Finset (Fin n)).erase (0 : Fin n), (y i) ^ 2)
        = ∑ i ∈ (Finset.univ : Finset (Fin n)).erase (0 : Fin n),
            (if i = (0 : Fin n) then 0 else (y i) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hne : i ≠ (0 : Fin n) := by
            simpa using (Finset.mem_erase.mp hi).1
          simp [hne]
    _ = ∑ i : Fin n, (if i = (0 : Fin n) then 0 else (y i) ^ 2) := by
          rw [Finset.sum_erase]
          simp

end Commons.Analysis.InnerProductSpace