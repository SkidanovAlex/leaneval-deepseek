import Mathlib
import Submission.Work.WilCrux.SheetDefs

namespace Work.WilCrux

open Classical

/-- For a finite set `s` of a linear order and its increasing enumeration `s.orderEmbOfFin h`,
the elements of `s` lying strictly below the `i`-th element are exactly the first `i` of them;
hence there are `i` of them. -/
lemma card_filter_lt_orderEmbOfFin {α : Type*} [LinearOrder α] (s : Finset α) {k : ℕ}
    (h : s.card = k) (i : Fin k) :
    (s.filter (fun x => x < s.orderEmbOfFin h i)).card = i.val := by
  classical
  set e := s.orderEmbOfFin h with he
  have hemem : ∀ j : Fin k, e j ∈ s := fun j => Finset.orderEmbOfFin_mem s h j
  have hlt : ∀ {a b : Fin k}, e a < e b ↔ a < b := fun {a b} => OrderEmbedding.lt_iff_lt e
  have hrange : ∀ x, x ∈ s ↔ ∃ j : Fin k, e j = x := by
    intro x
    rw [← Set.mem_range, Finset.range_orderEmbOfFin s h]
    simp
  have hfilter : s.filter (fun x => x < e i) =
      Finset.map e.toEmbedding (Finset.univ.filter (fun j : Fin k => j < i)) := by
    apply Finset.ext
    intro x
    rw [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨hxs, hxlt⟩
      obtain ⟨j, hj⟩ := (hrange x).mp hxs
      refine ⟨j, ?_, hj⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : e j < e i := by rw [hj]; exact hxlt
      exact hlt.mp this
    · rintro ⟨j, hj, hjx⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine ⟨?_, ?_⟩
      · rw [← hjx]; exact hemem j
      · rw [← hjx]; exact hlt.mpr hj
  rw [hfilter, Finset.card_map]
  have : (Finset.univ.filter (fun j : Fin k => j < i)) = Finset.Iio i := by
    ext j; simp [Finset.mem_Iio]
  rw [this, Fin.card_Iio]

/-- The `k`-th graph level of a word has exactly `k` graph levels below it. -/
theorem graphRank_graphIdx {N : ℕ} (w : Fin N → CellType) (k : Fin (nGraph N w)) :
    graphRank w (graphIdx w k) = k := by
  classical
  have h1 : (Finset.univ.filter (fun j : Fin N => graphBit (w j) = 1)).card = nGraph N w := by
    rw [nGraph_eq_card]
  have hgi : graphIdx w k =
      (Finset.univ.filter (fun j : Fin N => graphBit (w j) = 1)).orderEmbOfFin h1 k := rfl
  rw [hgi]
  have hgr : graphRank w
        ((Finset.univ.filter (fun j : Fin N => graphBit (w j) = 1)).orderEmbOfFin h1 k)
      = ((Finset.univ.filter (fun j : Fin N => graphBit (w j) = 1)).filter
          (fun i => i < (Finset.univ.filter (fun j : Fin N => graphBit (w j) = 1)).orderEmbOfFin h1 k)).card := by
    rw [graphRank, Finset.filter_filter]
    congr 1
    ext i
    simp [and_comm]
  rw [hgr]
  exact card_filter_lt_orderEmbOfFin _ h1 k

end Work.WilCrux
