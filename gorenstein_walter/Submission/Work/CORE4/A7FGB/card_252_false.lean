import Mathlib

namespace Work.CORE4.A7FGB

/-- Counting lemma: on a finite type `α`, the sum of the cardinalities of the fibres of a
function `f : α → ℕ` over a `Finset` `s` of values is at most `Nat.card α`.
The fibres over distinct values are disjoint subsets of `α`. -/
lemma sum_card_fibers_le {α : Type*} [Fintype α] (f : α → ℕ) (s : Finset ℕ) :
    ∑ m ∈ s, Nat.card {x : α // f x = m} ≤ Nat.card α := by
  classical
  have hdisj : (↑s : Set ℕ).PairwiseDisjoint
      (fun m => Finset.univ.filter (fun x : α => f x = m)) := by
    intro a _ b _ hab
    rw [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [Finset.mem_filter] at hx hy
    exact hab (hx.2.symm.trans hy.2)
  have hcard := Finset.card_biUnion hdisj
  have hsum_eq : (∑ m ∈ s, Nat.card {x : α // f x = m})
      = ∑ m ∈ s, (Finset.univ.filter (fun x : α => f x = m)).card := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hsum_eq, ← hcard]
  calc (s.biUnion (fun m => Finset.univ.filter (fun x : α => f x = m))).card
      ≤ (Finset.univ : Finset α).card := Finset.card_le_card (fun x _ => Finset.mem_univ x)
    _ = Nat.card α := by rw [Finset.card_univ, Nat.card_eq_fintype_card]

/-- There is no subgroup `R` of `A₇` of order `252` carrying the element counts
`|{g : orderOf g = 2}| ≥ 21`, `|{g : orderOf g = 3, 3-cycle}| ≥ 14`,
`|{g : orderOf g = 6}| ≥ 6` and `|{g : orderOf g = 7}| = 216`.

Indeed the fibres of `orderOf` over the four distinct values `2, 3, 6, 7` are pairwise
disjoint subsets of `↥R`, so their sizes sum to at most `|R| = 252`; but they are at least
`21 + 14 + 6 + 216 = 257`. -/
theorem card_252_false (R : Subgroup (alternatingGroup (Fin 7))) (hR : Nat.card R = 252)
    (hinv : 21 ≤ Nat.card {g : ↥R // orderOf g = 2})
    (h3 : 14 ≤ Nat.card {g : ↥R // orderOf g = 3 ∧ (g : Equiv.Perm (Fin 7)).support.card = 3})
    (h6 : 6 ≤ Nat.card {g : ↥R // orderOf g = 6})
    (h7 : Nat.card {g : ↥R // orderOf g = 7} = 216) : False := by
  haveI : Fintype ↥R := Fintype.ofFinite ↥R
  have hle := sum_card_fibers_le (fun g : ↥R => orderOf g) ({2, 3, 6, 7} : Finset ℕ)
  have hsum : (∑ m ∈ ({2, 3, 6, 7} : Finset ℕ), Nat.card {x : ↥R // orderOf x = m})
      = Nat.card {x : ↥R // orderOf x = 2} + Nat.card {x : ↥R // orderOf x = 3}
        + Nat.card {x : ↥R // orderOf x = 6} + Nat.card {x : ↥R // orderOf x = 7} := by
    norm_num [Finset.sum_insert]
    ring
  have h3le : Nat.card {g : ↥R // orderOf g = 3 ∧ (g : Equiv.Perm (Fin 7)).support.card = 3}
      ≤ Nat.card {g : ↥R // orderOf g = 3} := by
    apply Nat.card_mono
    · exact Set.toFinite _
    · intro x hx; exact hx.1
  rw [hsum] at hle
  omega

end Work.CORE4.A7FGB
