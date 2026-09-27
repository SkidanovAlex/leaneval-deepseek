import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic
import Submission.Work.PL.Generic.Hull
import Submission.Work.PL.Generic.exists_index_step
import Submission.Work.PL.Generic.mem_affineSpan_insert_of_mem_of_notMem

namespace Work.PL.Generic

open Set

/-- Unordering step: a general-position condition checked at each step of an enumeration `l` of the
free vertices (`hav` at step `j` for all `T ⊆ fz ∪ l.take j` and all `S ∈ Fixed`) holds for an
arbitrary `T ⊆ fz ∪ l.toFinset`.  Proof by minimal counterexample: let `l[m]` be the largest element
of `T` (in the enumeration order; `m > j` since `u = l[j]`), and put `T' = T \ {l[m]}`; writing
`y u` as an affine combination of `y '' (T' ∪ {l[m]}) ∪ S`, either the coefficient of `l[m]` is
non-zero, and then `y (l[m]) ∈ affineSpan (y '' (T' ∪ {u}) ∪ S)` with `T' ∪ {u} ⊆ fz ∪ l.take m`,
so `hav` at `m` gives `⊤` (a superset of our span), or it is zero, and `|T|` decreases. -/
theorem affineSpan_eq_top_of_forall_avoid {n : ℕ} {ι : Type*} [DecidableEq ι]
    (fz : Finset ι) (y : ι → PL.E n) (l : List ι) (hl : ∀ i, i ∈ l ↔ i ∉ fz) (hl' : l.Nodup)
    (Fixed : Finset (Finset (PL.E n)))
    (hav : ∀ j (hj : j < l.length), ∀ T : Finset ι, T ⊆ fz ∪ (l.take j).toFinset →
      ∀ S ∈ Fixed, y (l[j]) ∈
          (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) : Set (PL.E n)) →
        affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) = ⊤) :
    ∀ u, u ∉ fz → ∀ T : Finset ι, T ⊆ fz ∪ l.toFinset → u ∉ T → ∀ S ∈ Fixed,
      y u ∈ (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) : Set (PL.E n)) →
        affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) = ⊤ := by
  classical
  have main : ∀ N, ∀ T : Finset ι, T.card ≤ N → T ⊆ fz ∪ l.toFinset →
      ∀ u, u ∉ fz → u ∉ T → ∀ S ∈ Fixed,
        y u ∈ (affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) : Set (PL.E n)) →
        affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) = ⊤ := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N IH =>
      intro T hTN hTsub u hufz huT S hS hyu
      obtain ⟨j, hj, hlj⟩ := List.mem_iff_getElem.mp ((hl u).mpr hufz)
      by_cases hcase : T ⊆ fz ∪ (l.take j).toFinset
      · -- `T` sits inside the prefix: apply `hav` at `j` directly.
        exact hav j hj T hcase S hS (by rw [hlj]; exact hyu)
      · obtain ⟨m, hjm, hml, hlmT, hsub⟩ := exists_index_step fz l hl' hTsub huT hj hlj hcase
        have hT'sub : T.erase (l[m]) ⊆ fz ∪ l.toFinset :=
          (Finset.erase_subset (l[m]) T).trans hTsub
        have huT' : u ∉ T.erase (l[m]) := fun h => huT (Finset.mem_of_mem_erase h)
        by_cases hB : y u ∈ (affineSpan ℝ
            ((y '' ((T.erase (l[m]) : Finset ι) : Set ι)) ∪ (S : Set (PL.E n))) : Set (PL.E n))
        · -- Case (i): `y u` already lies in the span of the smaller set: induction.
          have hlt : (T.erase (l[m])).card < N :=
            lt_of_lt_of_le (Finset.card_erase_lt_of_mem hlmT) hTN
          have htop := IH (T.erase (l[m])).card hlt (T.erase (l[m])) le_rfl hT'sub
            u hufz huT' S hS hB
          have hmono : affineSpan ℝ ((y '' ((T.erase (l[m]) : Finset ι) : Set ι)) ∪
                (S : Set (PL.E n)))
              ≤ affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) := by
            apply affineSpan_mono
            exact Set.union_subset_union
              (Set.image_mono (Finset.coe_subset.mpr (Finset.erase_subset (l[m]) T)))
              (Subset.refl (S : Set (PL.E n)))
          exact top_le_iff.mp (htop ▸ hmono)
        · -- Case (ii): peel off `l[m]`.
          let T'' : Finset ι := T.erase (l[m]) ∪ {u}
          let Tu : Finset ι := T ∪ ({u} : Finset ι)
          have hT''eq : T'' = T.erase (l[m]) ∪ {u} := rfl
          have hTueq : Tu = T ∪ ({u} : Finset ι) := rfl
          have hsub'' : T'' ⊆ fz ∪ (l.take m).toFinset := hsub
          have hTe : (T : Set ι) = insert (l[m]) ((T.erase (l[m]) : Finset ι) : Set ι) := by
            rw [← Finset.coe_insert, Finset.insert_erase hlmT]
          have hset : ((y '' (T : Set ι)) ∪ (S : Set (PL.E n)))
              = ((y '' ((T.erase (l[m]) : Finset ι) : Set ι)) ∪ (S : Set (PL.E n)))
                  ∪ {y (l[m])} := by
            rw [hTe, Set.image_insert_eq, Set.insert_eq]
            ext z
            simp only [Set.mem_union, Set.mem_singleton_iff]
            tauto
          have hxmem : y u ∈ affineSpan ℝ
              (((y '' ((T.erase (l[m]) : Finset ι) : Set ι)) ∪ (S : Set (PL.E n)))
                ∪ {y (l[m])}) := by
            rw [← hset]
            exact hyu
          have hset2 : (((y '' ((T.erase (l[m]) : Finset ι) : Set ι)) ∪ (S : Set (PL.E n)))
                  ∪ {y u})
              = ((y '' (T'' : Set ι)) ∪ (S : Set (PL.E n))) := by
            rw [hT''eq, Finset.coe_union, Finset.coe_singleton, Set.image_union,
              Set.image_singleton]
            ext z
            simp only [Set.mem_union, Set.mem_singleton_iff]
            tauto
          have hp'' : y (l[m]) ∈ (affineSpan ℝ
              ((y '' (T'' : Set ι)) ∪ (S : Set (PL.E n))) : Set (PL.E n)) := by
            have hpeel := mem_affineSpan_insert_of_mem_of_notMem
              (s := ((y '' ((T.erase (l[m]) : Finset ι) : Set ι)) ∪ (S : Set (PL.E n))))
              hxmem hB
            rwa [hset2] at hpeel
          have htop := hav m hml T'' hsub'' S hS hp''
          have hWu : affineSpan ℝ ((y '' (Tu : Set ι)) ∪ (S : Set (PL.E n)))
              = affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) := by
            have hins : ((y '' (Tu : Set ι)) ∪ (S : Set (PL.E n)))
                = insert (y u) ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) := by
              rw [hTueq, Finset.coe_union, Finset.coe_singleton, Set.image_union,
                Set.image_singleton, Set.insert_eq]
              ext z
              simp only [Set.mem_union, Set.mem_singleton_iff]
              tauto
            rw [hins, affineSpan_insert_eq_affineSpan ℝ hyu]
          have hsub2 : T'' ⊆ Tu := by
            rw [hT''eq, hTueq]
            intro z hz
            rcases Finset.mem_union.mp hz with h' | h'
            · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase h')
            · exact Finset.mem_union_right _ h'
          have hmono2 : affineSpan ℝ ((y '' (T'' : Set ι)) ∪ (S : Set (PL.E n)))
              ≤ affineSpan ℝ ((y '' (T : Set ι)) ∪ (S : Set (PL.E n))) := by
            rw [← hWu]
            apply affineSpan_mono
            exact Set.union_subset_union
              (Set.image_mono (Finset.coe_subset.mpr hsub2)) (Subset.refl (S : Set (PL.E n)))
          exact top_le_iff.mp (htop ▸ hmono2)
  intro u hufz T hTsub huT S hS hyu
  exact main T.card T le_rfl hTsub u hufz huT S hS hyu

end Work.PL.Generic
