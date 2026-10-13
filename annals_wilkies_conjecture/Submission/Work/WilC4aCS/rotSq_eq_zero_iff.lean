import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

/-- A sum of squares of reals vanishes if and only if each summand vanishes. This is the general
principle behind `rotSq_eq_zero_iff`. -/
lemma sum_sq_eq_zero_iff {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i ^ 2) = 0 ↔ ∀ i, f i = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (f i))]
  constructor
  · intro h i
    exact sq_eq_zero_iff.mp (h i (Finset.mem_univ i))
  · intro h i _
    rw [h i]
    norm_num

theorem rotSq_eq_zero_iff {m : ℕ} (ψ : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) :
    Work.WilC4aCS.rotSq ψ x = 0 ↔ ∀ a b : Fin m, Work.WilC4aCS.rotTerm ψ x a b = 0 := by
  rw [rotSq_eq_sum m ψ x]
  rw [sum_sq_eq_zero_iff (fun p : Fin m × Fin m => rotTerm ψ x p.1 p.2)]
  constructor
  · intro h a b
    exact h (a, b)
  · intro h p
    exact h p.1 p.2

end Work.WilC4aCS
