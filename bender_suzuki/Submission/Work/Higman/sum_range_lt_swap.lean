import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

theorem sum_range_lt_swap {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → ℕ → M) :
    (∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => l < k), g k l)
      = (∑ k ∈ Finset.range n, ∑ l ∈ (Finset.range n).filter (fun l => k < l), g l k) := by
  -- Rewrite both filtered inner sums as indicator (if-then-else) sums over `range n`.
  simp only [Finset.sum_filter]
  -- Now both sides are double sums over `range n × range n`; the right-hand side is the
  -- left-hand side with the two summation indices exchanged (and `g`'s arguments swapped).
  rw [Finset.sum_comm (s := Finset.range n) (t := Finset.range n)
        (f := fun k l => (if k < l then g l k else 0))]

end Work.Higman
