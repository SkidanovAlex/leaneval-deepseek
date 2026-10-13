import Mathlib
import Submission.Work.WilC4.UnifDefs

set_option autoImplicit false
namespace Work.WilC4

/-- If `S` is the union of the members of a finite family `s` of order-convex sets, then
`S` has at most `s.card` order-convex components, so it cannot contain an `AltChain` of
length `s.card` (which is a witness for `s.card + 1` components).

The argument is by pigeonhole: the `s.card + 1` points `x j` of an `AltChain s.card S`
each lie in some member of `s`, so two of them, say `x a` and `x b` with `a < b`, lie in
the same order-convex member `I`.  Then `I` contains the order interval `[x a, x b]`,
hence also the separating point `y a` (since `x a < y a < x (a+1) ≤ x b`), contradicting
`y a ∉ S`. -/
theorem not_altChain_of_ordConnected {M : Type*} [LinearOrder M] {S : Set M}
    {s : Finset (Set M)} (hS : S = ⋃₀ (s : Set (Set M))) (hord : ∀ I ∈ s, I.OrdConnected) :
    ¬ AltChain s.card S := by
  rintro ⟨x, y, hx, hy⟩
  -- Each point of the chain lies in some member of the family.
  have key : ∀ j, ∃ I : Set M, I ∈ s ∧ x j ∈ I := fun j => by
    have hj : x j ∈ ⋃₀ (s : Set (Set M)) := hS ▸ hx j
    rw [Set.mem_sUnion] at hj
    exact hj
  choose I hIs hxI using key
  -- Pigeonhole: two indices share the same member.
  obtain ⟨a, -, b, -, hab, hIab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := s) (f := I)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega) (fun k _ => hIs k)
  -- An ordered pair of indices with equal image is impossible.
  have step : ∀ a b : Fin (s.card + 1), a < b → I a = I b → False := by
    intro a b hab hIab
    have ha : a.val < s.card := by
      have h1 := a.isLt
      have h2 := b.isLt
      have h3 : a.val < b.val := hab
      omega
    let a' : Fin s.card := ⟨a.val, ha⟩
    have hcs : Fin.castSucc a' = a := Fin.ext rfl
    have hya := hy a'
    have hlt1 : x a < y a' := by rw [← hcs]; exact hya.2.1
    have hsuc : Fin.succ a' ≤ b := by
      rw [Fin.le_def]
      have h2 := b.isLt
      have h3 : a.val < b.val := hab
      show a.val + 1 ≤ b.val
      omega
    have hstrict : StrictMono x := fun u v huv => altChain_lt hy huv
    have hle2 : x (Fin.succ a') ≤ x b := hstrict.monotone hsuc
    have hmem : y a' ∈ Set.Icc (x a) (x b) :=
      ⟨le_of_lt hlt1, le_of_lt (lt_of_lt_of_le hya.2.2 hle2)⟩
    have hbI : x b ∈ I a := by rw [hIab]; exact hxI b
    have hsub := (hord (I a) (hIs a)).out (hxI a) hbI
    have hyS : y a' ∈ S := by
      rw [hS, Set.mem_sUnion]
      exact ⟨I a, hIs a, hsub hmem⟩
    exact hya.1 hyS
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact step a b hlt hIab
  · exact step b a hlt hIab.symm

end Work.WilC4
