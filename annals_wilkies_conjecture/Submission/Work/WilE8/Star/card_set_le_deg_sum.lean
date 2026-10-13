import Mathlib
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Star.starPiece_set_eq_empty_or_cube

namespace Work.WilE8.Star

/-- Counting lemma.

Let `L` be a list of objects of type `α`, each carrying a "value" `f a : β` and a "degree"
`g a : ℕ`.  Suppose every object of degree `0` has its value inside a fixed finset `z` of `β`.
Then the number of *distinct* values occurring in `L` is at most `z.card` plus the total degree
`(L.map g).sum`.

The point is that objects of degree `0` can only contribute the at most `z.card` values of `z`,
while the objects of positive degree are no more numerous than their degree sum.

The proof is a (tight) induction on the list, with the invariant
`#(L.map f).toFinset ≤ (L.map g).sum + #((L.map f).toFinset ∩ z)`: the intersection counts the
values already known to lie in `z`. -/
theorem card_toFinset_map_le_sum_add {α β : Type*} [DecidableEq β]
    (L : List α) (f : α → β) (g : α → ℕ) (z : Finset β)
    (hz : ∀ a, g a = 0 → f a ∈ z) :
    (L.map f).toFinset.card ≤ (L.map g).sum + z.card := by
  have key : ∀ L : List α,
      (L.map f).toFinset.card ≤ (L.map g).sum + ((L.map f).toFinset ∩ z).card := by
    intro L
    induction L with
    | nil => simp
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
      by_cases hmem : f a ∈ (t.map f).toFinset
      · rw [Finset.insert_eq_of_mem hmem]
        omega
      · rw [Finset.card_insert_of_notMem hmem]
        by_cases hza : f a ∈ z
        · have h1 : insert (f a) ((t.map f).toFinset ∩ z) = insert (f a) (t.map f).toFinset ∩ z := by
            rw [Finset.insert_inter_distrib, Finset.insert_eq_of_mem hza]
          have h2 : (insert (f a) (t.map f).toFinset ∩ z).card
              = ((t.map f).toFinset ∩ z).card + 1 := by
            rw [← h1, Finset.card_insert_of_notMem]
            exact fun h => hmem (Finset.mem_inter.mp h).1
          omega
        · have hg1 : 1 ≤ g a := Nat.one_le_iff_ne_zero.mpr (fun h0 => hza (hz a h0))
          have hsub : (t.map f).toFinset ∩ z ⊆ insert (f a) (t.map f).toFinset ∩ z :=
            fun x hx => Finset.mem_inter.mpr
              ⟨Finset.mem_insert_of_mem (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩
          have h3 : ((t.map f).toFinset ∩ z).card ≤ (insert (f a) (t.map f).toFinset ∩ z).card :=
            Finset.card_le_card hsub
          omega
  calc (L.map f).toFinset.card
      ≤ (L.map g).sum + ((L.map f).toFinset ∩ z).card := key L
    _ ≤ (L.map g).sum + z.card := by
        have hz' : ((L.map f).toFinset ∩ z).card ≤ z.card :=
          Finset.card_le_card Finset.inter_subset_right
        omega

theorem card_set_le_deg_sum {n : ℕ} (L : List (WilkiesDesign.E.StarPiece n)) :
    (L.map fun P => P.set).toFinset.card ≤ (L.map fun P => P.X.deg).sum + 2 := by
  classical
  have h := card_toFinset_map_le_sum_add L (fun P => P.set) (fun P => P.X.deg)
    ({∅, WilkiesDesign.E.cubeC n} : Finset (Set (Fin n → ℝ)))
    (fun P hP => by
      rcases starPiece_set_eq_empty_or_cube P hP with h | h
      · rw [h]; simp
      · rw [h]; simp)
  have h2 : ({∅, WilkiesDesign.E.cubeC n} : Finset (Set (Fin n → ℝ))).card ≤ 2 :=
    Finset.card_le_two
  omega

end Work.WilE8.Star
