import Mathlib
import Submission.Work.WilCrux.SheetDefs

namespace Work.WilCrux

/-! ## Counting the elements of a finset below an `orderEmbOfFin` value

`bandIdx w` is the increasing enumeration of the band levels of the word `w`, while `bandRank w j`
counts the band levels strictly below `j`.  The fact that these are inverse to one another is an
instance of the following statement about an arbitrary finset of a linear order: the number of
elements of `s` lying strictly below the `i`-th element of the increasing enumeration of `s` is
exactly `i`. -/

/-- The elements of `s` strictly below the `i`-th element of the increasing enumeration of `s`
are exactly the images of `0, …, i-1`. -/
theorem filter_lt_orderEmbOfFin_eq {α : Type*} [LinearOrder α]
    (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.filter (fun x => x < s.orderEmbOfFin h i)
      = (Finset.Iio i).map (s.orderEmbOfFin h).toEmbedding := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio]
  constructor
  · rintro ⟨hxs, hxlt⟩
    have hxr : x ∈ Set.range (s.orderEmbOfFin h) := by
      rw [Finset.range_orderEmbOfFin]; exact hxs
    obtain ⟨j, hj⟩ := hxr
    refine ⟨j, ?_, hj⟩
    rw [← hj] at hxlt
    exact (s.orderEmbOfFin h).lt_iff_lt.mp hxlt
  · rintro ⟨j, hj, hjx⟩
    refine ⟨?_, ?_⟩
    · rw [← hjx]; exact Finset.orderEmbOfFin_mem s h j
    · rw [← hjx]; exact (s.orderEmbOfFin h).lt_iff_lt.mpr hj

/-- The number of elements of a finset `s` of cardinality `k` lying strictly below the `i`-th
element of the increasing enumeration of `s` is `i`. -/
theorem card_filter_lt_orderEmbOfFin {α : Type*} [LinearOrder α]
    (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    (s.filter (fun x => x < s.orderEmbOfFin h i)).card = (i : ℕ) := by
  rw [filter_lt_orderEmbOfFin_eq s h i, Finset.card_map, Fin.card_Iio]

/-- The band levels of the word `w`, counted below `bandIdx w k`, are exactly `k` in number. -/
theorem bandRank_bandIdx {N : ℕ} (w : Fin N → CellType) (k : Fin (nBand N w)) :
    bandRank w (bandIdx w k) = k := by
  have hgen := card_filter_lt_orderEmbOfFin
      (Finset.univ.filter (fun j : Fin N => bandBit (w j) = 1))
      ((nBand_eq_card N w).symm) k
  unfold bandRank
  rw [show bandIdx w k =
      (Finset.univ.filter (fun j : Fin N => bandBit (w j) = 1)).orderEmbOfFin
        ((nBand_eq_card N w).symm) k from by
    unfold bandIdx
    exact congrArg
      (fun hp => ((Finset.univ.filter (fun j : Fin N => bandBit (w j) = 1)).orderEmbOfFin hp) k)
      (Subsingleton.elim _ _)]
  rw [← hgen]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

end Work.WilCrux
