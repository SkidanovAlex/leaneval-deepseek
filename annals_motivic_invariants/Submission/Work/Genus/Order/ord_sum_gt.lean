import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.min_ord_le_ord_add

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Order

open Polynomial

/-- **The order of vanishing of the zero rational function is `0`** (the convention of
`Polynomial.multiplicity`: the reduced form of `0` is `0/1` and both multiplicities vanish). -/
@[simp]
theorem ord_zero {F : Type*} [Field F] (π : Polynomial F) :
    Work.Genus.ord π (0 : RatFunc F) = 0 := by
  simp [Work.Genus.ord]

/-- **The strict non-archimedean bound for a finite sum.**  If every summand `t i` (`i ∈ S`) has
order of vanishing at the place of `π` strictly bigger than a *negative* integer `c`, then so does
the whole sum.  The negativity of `c` is exactly what makes the statement true for the empty sum
(and, more generally, for a sum that cancels to `0`): the order of `0` is `0` by convention, which
is bigger than `c` precisely because `c < 0`.

The proof is the usual ultrametric induction on the finset: adding a term either produces `0`, whose
order is `0 > c`, or one of the two summands vanishes, or both are non-zero and
`min_ord_le_ord_add` bounds the order of the sum below by the minimum of the two orders. -/
theorem ord_sum_gt {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π)
    {S : Finset ℕ} {t : ℕ → RatFunc F} {c : ℤ} (hc : c < 0)
    (h : ∀ i ∈ S, c < Work.Genus.ord π (t i)) :
    c < Work.Genus.ord π (∑ i ∈ S, t i) := by
  classical
  induction S using Finset.induction with
  | empty => simpa [Work.Genus.ord] using hc
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have hA : c < Work.Genus.ord π (t a) := h a (Finset.mem_insert_self a S)
    have hS : ∀ i ∈ S, c < Work.Genus.ord π (t i) :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hB : c < Work.Genus.ord π (∑ i ∈ S, t i) := ih hS
    by_cases hab : t a + ∑ i ∈ S, t i = 0
    · simpa [hab, Work.Genus.ord] using hc
    · by_cases hAa : t a = 0
      · rw [hAa, zero_add]; exact hB
      · by_cases hBa : (∑ i ∈ S, t i) = 0
        · rw [hBa, add_zero]; exact hA
        · exact lt_of_lt_of_le (lt_min hA hB)
            (min_ord_le_ord_add hπ hAa hBa hab)

end Work.Genus.Order
