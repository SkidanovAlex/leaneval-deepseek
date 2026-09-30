import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.sd3_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

theorem goodPairs_card_eq_sum {f : ℕ → ℂ} {pol : ℝ → Polynomial ℝ} {η H a b : ℝ}
    {fam : Finset ℝ} :
    (Work.BMF.goodPairs f pol η H a b fam).card =
      ∑ p ∈ Work.BMF.primesIn a b,
        ((fam.filter (fun y => η * (H / (p : ℝ)) ≤
          ‖Work.BMF.corr f (Work.BMF.dil (p : ℝ) (pol y)) (y / (p : ℝ)) (H / (p : ℝ))‖)).card) := by
  classical
  -- `goodPairs` is the filtered product `fam ×ˢ primesIn a b`.
  rw [Work.BMF.goodPairs]
  -- Count a filtered finset by the sum of its indicator.
  rw [Finset.card_filter]
  -- Split the sum over the product into a double sum, then exchange the order.
  rw [Finset.sum_product]
  rw [Finset.sum_comm]
  -- The inner sum over `fam` of the indicator is the cardinality of the fiber.
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.card_filter]

end Work.BMF.SD
