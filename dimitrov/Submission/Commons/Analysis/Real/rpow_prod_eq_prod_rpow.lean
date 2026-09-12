import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.SimpleRing.Principal

noncomputable section
open scoped BigOperators

namespace Commons.Analysis.Real

/-! Real `rpow` distributes over finite products of nonnegative factors. -/
theorem rpow_prod_eq_prod_rpow {ι : Type*} [Fintype ι] (f : ι → ℝ) (z : ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (∏ i : ι, f i) ^ z = ∏ i : ι, (f i) ^ z := by
  classical
  have main : ∀ s : Finset ι, (∏ i ∈ s, f i) ^ z = ∏ i ∈ s, (f i) ^ z := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp [Real.one_rpow]
    · intro a s has ih
      rw [Finset.prod_insert has, Real.mul_rpow (hf a) (Finset.prod_nonneg (fun i hi => hf i)), ih]
      rw [Finset.prod_insert has]
  simpa using main Finset.univ

end Commons.Analysis.Real