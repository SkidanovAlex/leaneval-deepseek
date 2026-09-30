import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The number of monomials of degree `≤ T` in `ℓ` variables

Multi-indices `β : Fin ℓ → ℕ` with `∑ i, β i ≤ T` index the monomials of degree at most `T`
in `ℓ` indeterminates.  This file proves that there are exactly `C(T + ℓ, ℓ)` of them.

The proof is a stars-and-bars bijection: adding the slack variable `T - ∑ i, β i` exhibits the
set of such `β` as the set of functions `Fin (ℓ+1) → ℕ` summing to `T`, whose cardinality is the
binomial coefficient by `Finset.card_finsuppAntidiag_nat_eq_choose`.
-/

namespace Work.BW

open Finset

/-- Stars and bars: the number of functions `Fin k → ℕ` with `∑ i, f i = n` is
`(k + n - 1).choose n`.  This is `Finset.card_finsuppAntidiag_nat_eq_choose` transported across
the finite-support equivalence `Finsupp.equivFunOnFinite`. -/
private theorem card_piAntidiag_univ {k n : ℕ} :
    (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).card = (k + n - 1).choose n := by
  have h1 : (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).card
      = ((Finset.univ : Finset (Fin k)).finsuppAntidiag n).card := by
    refine Finset.card_equiv (Finsupp.equivFunOnFinite.symm) ?_
    intro f
    simp only [Finset.mem_piAntidiag, Finset.mem_finsuppAntidiag,
      Finsupp.coe_equivFunOnFinite_symm, Finset.mem_univ, subset_univ, imp_true_iff, and_true]
  rw [h1, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin]

/-- The multi-indices `β : Fin ℓ → ℕ` with `∑ i, β i ≤ T` are in bijection with the functions
`Fin (ℓ+1) → ℕ` summing to `T`: the bijection appends the slack variable `T - ∑ i, β i`
(`Fin.cons`), with inverse given by the tail `Fin.tail`.  The extra constraint
`β i < T + 1` is implied by `∑ i, β i ≤ T`. -/
private theorem card_piFinset_filter_sum_le (ℓ T : ℕ) :
    ((Fintype.piFinset (fun _ : Fin ℓ => Finset.range (T + 1))).filter
      (fun β : Fin ℓ → ℕ => ∑ i, β i ≤ T)).card
      = (Finset.piAntidiag (Finset.univ : Finset (Fin (ℓ + 1))) T).card := by
  classical
  refine Finset.card_bij' (fun β _ => Fin.cons (T - ∑ i, β i) β) (fun g _ => Fin.tail g)
    ?_ ?_ ?_ ?_
  · -- the appended slack makes the sum equal `T`
    intro β hβ
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    have hβle : ∑ i, β i ≤ T := (Finset.mem_filter.mp hβ).2
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega
  · -- a function summing to `T` has tail summing to `≤ T`, with entries `< T + 1`
    intro g hg
    have hg' : ∑ i : Fin (ℓ + 1), g i = T := (Finset.mem_piAntidiag.mp hg).1
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff,
      Fin.tail]
    constructor
    · intro i
      calc g i.succ ≤ ∑ j : Fin (ℓ + 1), g j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i.succ)
        _ = T := hg'
    · have hsplit : (∑ i : Fin (ℓ + 1), g i) = g 0 + ∑ i : Fin ℓ, g i.succ :=
        Fin.sum_univ_succ g
      omega
  · -- `Fin.tail ∘ Fin.cons` is the identity
    intro β hβ
    exact Fin.tail_cons _ _
  · -- `Fin.cons ∘ Fin.tail` is the identity, since the slack is the forgotten first entry
    intro g hg
    have hg' : ∑ i : Fin (ℓ + 1), g i = T := (Finset.mem_piAntidiag.mp hg).1
    have h : T - ∑ i : Fin ℓ, Fin.tail g i = g 0 := by
      have hsplit : (∑ i : Fin (ℓ + 1), g i) = g 0 + ∑ i : Fin ℓ, g i.succ :=
        Fin.sum_univ_succ g
      have htail : (∑ i : Fin ℓ, Fin.tail g i) = ∑ i : Fin ℓ, g i.succ :=
        Finset.sum_congr rfl (fun i _ => by simp only [Fin.tail])
      rw [htail]
      omega
    rw [h, Fin.cons_self_tail]

/-- The monomials of degree `≤ T` in `ℓ` variables: there are `C(T+ℓ,ℓ)` multi-indices
`β : Fin ℓ → ℕ` with `∑ βᵢ ≤ T`. -/
theorem card_weight_le {ℓ T : ℕ} :
    ((Fintype.piFinset (fun _ : Fin ℓ => Finset.range (T + 1))).filter
      (fun β : Fin ℓ → ℕ => ∑ i, β i ≤ T)).card = (T + ℓ).choose ℓ := by
  rw [card_piFinset_filter_sum_le ℓ T, card_piAntidiag_univ (k := ℓ + 1) (n := T)]
  have h : ℓ + 1 + T - 1 = T + ℓ := by omega
  rw [h]
  exact Nat.choose_symm_add

end Work.BW
