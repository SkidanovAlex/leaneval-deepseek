import Mathlib

namespace Work.WilE4.CAD

theorem multiset_card_eq_sum_filter_of_disjoint {α : Type*} [DecidableEq α] (m : Multiset α)
    (R : Finset α) (P : α → α → Prop) [∀ z, DecidablePred (P z)]
    (hdisj : ∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → ∀ w, P z w → P z' w → False)
    (hcov : ∀ w ∈ m, ∃ z ∈ R, P z w) :
    m.card = ∑ z ∈ R, (m.filter (fun w => P z w)).card := by
  classical
  -- Induct on the multiset.  Each element `w` of `m` is covered by a unique
  -- `z ∈ R`, so summing, over `z ∈ R`, the number of elements of `m` satisfying
  -- `P z w` counts every element of `m` exactly once.
  have aux : ∀ (m : Multiset α), (∀ w ∈ m, ∃ z ∈ R, P z w) →
      m.card = ∑ z ∈ R, (m.filter (fun w => P z w)).card := by
    intro m
    induction m using Multiset.induction_on with
    | empty => intro _; simp
    | cons w m' ih =>
        intro hcov
        -- the induction hypothesis applies to the tail
        have hcov' : ∀ w' ∈ m', ∃ z ∈ R, P z w' :=
          fun w' hw' => hcov w' (Multiset.mem_cons_of_mem hw')
        -- filtering the cons adds one for each `z` with `P z w`
        have hfilter : ∀ z, ((w ::ₘ m').filter (fun w => P z w)).card
            = (if P z w then 1 else 0) + (m'.filter (fun w => P z w)).card := by
          intro z
          rw [Multiset.filter_cons, Multiset.card_add]
          by_cases h : P z w
          · simp [h]
          · simp [h]
        -- `w` is covered by exactly one `z ∈ R`, so the indicator sum is `1`
        have hsum_one : ∑ z ∈ R, (if P z w then 1 else 0) = 1 := by
          obtain ⟨z0, hz0R, hz0P⟩ := hcov w (Multiset.mem_cons_self w m')
          rw [Finset.sum_eq_single_of_mem z0 hz0R]
          · simp [hz0P]
          · intro b hbR hbz
            have hPb : ¬ P b w :=
              fun hPb => hdisj z0 hz0R b hbR (Ne.symm hbz) w hz0P hPb
            simp [hPb]
        rw [Multiset.card_cons, Finset.sum_congr rfl (fun z _ => hfilter z),
          Finset.sum_add_distrib, hsum_one, ← ih hcov']
        exact Nat.add_comm _ _
  exact aux m hcov

end Work.WilE4.CAD
