import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic

namespace Work.CORE3

open Work.GW2

/-- Combinatorial identity behind Bender 1981 §3 (3): summing `b_n` over all `n` counts the
nontrivial cosets of `Hh`.  (`bCount Hh n` is the number of cosets `≠ Hh` of `G ⧸ Hh` containing
exactly `n` involutions; `Work.CORE2A.cosetInvCount_le` bounds `n` by `Nat.card Hh`.)  Used by
`Case1bCountProp` and `Case1bIndexProp`. -/
theorem BCountSum (G : Type) [Group G] [Finite G] (Hh : Subgroup G) :
    ∑ n ∈ Finset.range (Nat.card Hh + 1), bCount Hh n = Hh.index - 1 := by
  classical
  haveI : Fintype (G ⧸ Hh) := Fintype.ofFinite _
  -- `bCount` is the cardinality of a fibre of the coset-involution count.
  have hbc : ∀ n : ℕ, bCount Hh n =
      (Finset.univ.filter (fun c : G ⧸ Hh =>
        c ≠ ((1 : G) : G ⧸ Hh) ∧ cosetInvCount Hh (Quotient.out c) = n)).card := by
    intro n
    rw [bCount, Set.ncard_eq_toFinset_card']
    rw [Set.toFinset_ofPred]
  -- summing the fibre sizes over the range of possible values counts all nontrivial cosets
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh)))
    (t := Finset.range (Nat.card Hh + 1))
    (f := fun c : G ⧸ Hh => cosetInvCount Hh (Quotient.out c))
    (by
      intro c _
      simp only [Finset.mem_coe, Finset.mem_range]
      exact Nat.lt_succ_of_le (Work.CORE2A.cosetInvCount_le Hh (Quotient.out c)))
  calc
    ∑ n ∈ Finset.range (Nat.card Hh + 1), bCount Hh n
        = ∑ n ∈ Finset.range (Nat.card Hh + 1),
            (Finset.univ.filter (fun c : G ⧸ Hh =>
              c ≠ ((1 : G) : G ⧸ Hh) ∧ cosetInvCount Hh (Quotient.out c) = n)).card :=
          Finset.sum_congr rfl (fun n _ => hbc n)
    _ = ∑ n ∈ Finset.range (Nat.card Hh + 1),
            ((Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh))).filter
              (fun c : G ⧸ Hh => cosetInvCount Hh (Quotient.out c) = n)).card := by
          apply Finset.sum_congr rfl
          intro n _
          congr 1
          rw [Finset.filter_filter]
    _ = (Finset.univ.filter (fun c : G ⧸ Hh => c ≠ ((1 : G) : G ⧸ Hh))).card := hfib.symm
    _ = Hh.index - 1 := by
          rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Work.CORE3
