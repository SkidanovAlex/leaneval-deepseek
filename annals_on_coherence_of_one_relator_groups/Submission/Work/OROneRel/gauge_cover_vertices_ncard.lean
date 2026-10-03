import Mathlib
import Submission.Work.OROneRel.gaugeLevelDefs
import Submission.Work.OROneRel.gauge_walk_defs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.MagnusGenDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The number of distinct elements of a finset, read as a set, is its cardinality. -/
theorem ncard_coe_finset_int (F : Finset ℤ) : (↑F : Set ℤ).ncard = F.card := by
  simp [Set.ncard_eq_toFinset_card]

/-- For a list of length at least two, an element occurs in the list iff it occurs among the entries
of the list with its last entry removed, or among those of the list with its first entry removed. -/
theorem mem_toFinset_iff_mem_dropLast_or_tail {l : List ℤ} (hl : 2 ≤ l.length) (i : ℤ) :
    i ∈ l.toFinset ↔ i ∈ l.dropLast ∨ i ∈ l.tail := by
  rw [List.mem_toFinset]
  refine ⟨fun hi => ?_, fun h => h.elim (fun h' => List.dropLast_subset l h')
      (fun h' => List.tail_subset l h')⟩
  match l with
  | [] => simp at hl
  | [_] => simp at hl
  | x :: y :: ys =>
    rw [List.dropLast_cons_of_ne_nil (by simp : (y :: ys) ≠ [])]
    rcases List.mem_cons.mp hi with rfl | hi
    · exact Or.inl (List.mem_cons_self ..)
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem y hi)

/-- The vertices of the cover that are touched by the decorated word `decor c 0 (wordOf u)` -- the
union of the source levels and the target levels of its decorated letters -- are exactly the distinct
levels visited by the walk `running c 0 (wordOf u)`. -/
theorem gauge_cover_vertices_ncard {α : Type u} (c : α → ℤ) (u : FreeGroup α)
    (hne : Work.OROneRel.wordOf u ≠ []) :
    ({i : ℤ | ∃ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u), Work.OROneRel.coverSrc c p = i} ∪
        {i : ℤ | ∃ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u), Work.OROneRel.coverTgt c p = i}).ncard =
      (Work.OROneRel.running c 0 (Work.OROneRel.wordOf u)).toFinset.card := by
  have hlen : 2 ≤ (running c 0 (wordOf u)).length := by
    rw [running_length]
    have hpos : 0 < (wordOf u).length := List.length_pos_iff.mpr hne
    omega
  have hset : ({i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverSrc c p = i} ∪
      {i : ℤ | ∃ p ∈ decor c 0 (wordOf u), coverTgt c p = i}) =
      ↑(running c 0 (wordOf u)).toFinset := by
    ext i
    simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe]
    rw [mem_toFinset_iff_mem_dropLast_or_tail hlen i,
      ← decor_map_coverSrc c 0 (wordOf u), ← decor_map_coverTgt c 0 (wordOf u),
      List.mem_map, List.mem_map]
  rw [hset]
  exact ncard_coe_finset_int _

end Work.OROneRel
