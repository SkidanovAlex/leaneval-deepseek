import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.star_algebra
import Submission.Work.WilE7.subPf_algebra
import Submission.Work.WilE7.set_glue

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-!
# Union of a finite family of `*`-sets / sub-Pfaffian sets

`Work.WilE7.set_glue` identifies `⋃₀ (s : Set _)` with the union of the members of a
finset `s`.  The present file shows that the two complexity predicates of area E are
stable under such a finite union:

* a finite union of `*`-sets with a common format `F` and a common degree `D` is a
  `*`-set with format `F` and degree `s.card * D` (the degrees add up, the formats do
  not grow, because merging two pieces keeps the format);
* a finite union of sub-Pfaffian sets is sub-Pfaffian (no complexity bound is kept in
  `SubPf`).

Both are proved by induction on the finset, splitting off one element with
`Finset.induction_on`, using the binary merging operations `Work.WilE8.Star.union2` and
`SubPfAlg.subPf_union`.
-/

theorem s_union_tools :
    (∀ {n : ℕ} (s : Finset (Set (Fin n → ℝ))) (F D : ℕ),
        (∀ κ ∈ s, WilkiesDesign.E.Star F D n κ) →
        WilkiesDesign.E.Star F (s.card * D) n (⋃₀ (s : Set (Set (Fin n → ℝ))))) ∧
    (∀ {n : ℕ} (s : Finset (Set (Fin n → ℝ))),
        (∀ κ ∈ s, WilkiesDesign.E.SubPf n κ) →
        WilkiesDesign.E.SubPf n (⋃₀ (s : Set (Set (Fin n → ℝ))))) := by
  classical
  refine ⟨?_, ?_⟩
  · intro n s F D h
    revert h
    refine Finset.induction_on (motive := fun t : Finset (Set (Fin n → ℝ)) =>
        (∀ κ ∈ t, WilkiesDesign.E.Star F D n κ) →
        WilkiesDesign.E.Star F (t.card * D) n (⋃₀ (t : Set (Set (Fin n → ℝ))))) s ?_ ?_
    · intro _
      rw [Finset.card_empty, Nat.zero_mul, Finset.coe_empty, Set.sUnion_empty]
      exact Work.WilE8.Star.empty F n
    · intro a t ht ih h
      have hUnion : (⋃₀ ((insert a t : Finset (Set (Fin n → ℝ))) : Set (Set (Fin n → ℝ))))
          = a ∪ ⋃₀ (t : Set (Set (Fin n → ℝ))) := by
        rw [Finset.coe_insert, Set.sUnion_insert]
      rw [Finset.card_insert_of_notMem ht, hUnion]
      have ha : WilkiesDesign.E.Star F D n a := h a (Finset.mem_insert_self a t)
      have ht' : WilkiesDesign.E.Star F (t.card * D) n
          (⋃₀ (t : Set (Set (Fin n → ℝ)))) :=
        ih (fun κ hκ => h κ (Finset.mem_insert_of_mem hκ))
      have hunion := Work.WilE8.Star.union2 ha ht'
      have hle : D + t.card * D ≤ (t.card + 1) * D := by
        have hEq : (t.card + 1) * D = D + t.card * D := by ring
        exact le_of_eq hEq.symm
      exact Work.WilE8.Star.mono hunion le_rfl hle
  · intro n s h
    revert h
    refine Finset.induction_on (motive := fun t : Finset (Set (Fin n → ℝ)) =>
        (∀ κ ∈ t, WilkiesDesign.E.SubPf n κ) →
        WilkiesDesign.E.SubPf n (⋃₀ (t : Set (Set (Fin n → ℝ))))) s ?_ ?_
    · intro _
      rw [Finset.coe_empty, Set.sUnion_empty]
      exact SubPfAlg.subPf_empty n
    · intro a t ht ih h
      rw [Finset.coe_insert, Set.sUnion_insert]
      exact SubPfAlg.subPf_union (h a (Finset.mem_insert_self a t))
        (ih (fun κ hκ => h κ (Finset.mem_insert_of_mem hκ)))

end Work.WilE7
