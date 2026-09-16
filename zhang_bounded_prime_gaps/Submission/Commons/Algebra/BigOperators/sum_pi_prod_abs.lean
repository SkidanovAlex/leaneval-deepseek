import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

namespace Commons.Algebra.BigOperators

theorem sum_pi_prod_abs {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (a : ∀ i : ι, κ i → ℝ) :
    (∑ x : (∀ i : ι, κ i), ∏ i : ι, |a i (x i)|) =
      ∏ i : ι, ∑ y : κ i, |a i y| := by
  exact (Fintype.prod_sum (ι := ι) (κ := κ) (R := ℝ) fun i y => |a i y|).symm

end Commons.Algebra.BigOperators