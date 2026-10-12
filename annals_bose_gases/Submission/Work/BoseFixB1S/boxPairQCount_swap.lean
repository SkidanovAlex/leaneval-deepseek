import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseFixB1S.BoxFlatAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open scoped BigOperators

/-- The fibre of `pairSet N` over a disjoint pair of blocks `(S,T)`: the pairs of distinct
indices whose first entry lies in `S` and whose second entry lies in `T`.  It is the full product
`S × T`, precisely because `S` and `T` are disjoint. -/
theorem pairSet_filter_eq_product {N : ℕ} {p : Finset (Fin N) × Finset (Fin N)}
    (hp : Disjoint p.1 p.2) :
    (Submission.BoseGases.pairSet N).filter (fun q : Fin N × Fin N =>
        q.1 ∈ p.1 ∧ q.2 ∈ p.2) = p.1 ×ˢ p.2 := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_product, Submission.BoseGases.pairSet,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun hEq => ?_, h1, h2⟩
    rw [hEq] at h1
    exact Finset.disjoint_left.mp hp h1 h2

/-- The size of that fibre: `|S| · |T|`. -/
theorem pairSet_filter_card {N : ℕ} {p : Finset (Fin N) × Finset (Fin N)}
    (hp : Disjoint p.1 p.2) :
    ((Submission.BoseGases.pairSet N).filter (fun q : Fin N × Fin N =>
        q.1 ∈ p.1 ∧ q.2 ∈ p.2)).card = p.1.card * p.2.card := by
  rw [pairSet_filter_eq_product hp, Finset.card_product]

/-- The number of ordered pairs of distinct indices with first entry in `S` and second entry in
`T`, counted over `pairSet N`, is `|S| · |T|` (as a real number). -/
theorem sum_pairSet_indicator_eq_card_mul {N : ℕ} {p : Finset (Fin N) × Finset (Fin N)}
    (hp : Disjoint p.1 p.2) :
    (∑ q ∈ Submission.BoseGases.pairSet N,
        (if q.1 ∈ p.1 ∧ q.2 ∈ p.2 then (1 : ℝ) else 0))
      = (p.1.card : ℝ) * (p.2.card : ℝ) := by
  have h := Finset.card_filter (fun q : Fin N × Fin N => q.1 ∈ p.1 ∧ q.2 ∈ p.2)
    (Submission.BoseGases.pairSet N)
  rw [pairSet_filter_card hp] at h
  exact_mod_cast h.symm

/-- **Double counting.**  Summing a function of a pair of disjoint blocks over the ordered pairs
of distinct indices lying in the blocks, and then over the blocks, is the same as weighting each
pair of blocks by the product of their cardinalities. -/
theorem boxPairQCount_swap {N : ℕ}
    (F : Finset (Fin N) × Finset (Fin N) → ℝ) :
    (∑ q ∈ Submission.BoseGases.pairSet N,
        ∑ p ∈ (Work.BoseFixB1S.disjPairs N).filter (fun p => q.1 ∈ p.1 ∧ q.2 ∈ p.2), F p)
      = ∑ p ∈ Work.BoseFixB1S.disjPairs N,
          ((p.1.card : ℝ) * (p.2.card : ℝ)) * F p := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hsplit : (∑ q ∈ Submission.BoseGases.pairSet N,
        (if q.1 ∈ p.1 ∧ q.2 ∈ p.2 then F p else 0))
      = (∑ q ∈ Submission.BoseGases.pairSet N,
          (if q.1 ∈ p.1 ∧ q.2 ∈ p.2 then (1 : ℝ) else 0)) * F p := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hc : q.1 ∈ p.1 ∧ q.2 ∈ p.2 <;> simp [hc]
  rw [hsplit, sum_pairSet_indicator_eq_card_mul (mem_disjPairs.mp hp)]

end Work.BoseFixB1S
