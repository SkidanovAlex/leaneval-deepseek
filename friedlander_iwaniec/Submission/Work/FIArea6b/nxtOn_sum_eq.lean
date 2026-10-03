import Mathlib
import Submission.Work.FIArea6b.Basic

namespace Work.FIArea6b

/-!
## The successor map `nxtOn` on a finite set of integers

For a nonempty finite set `T ⊆ ℤ`, the map `t ↦ nxtOn T t` (the least element of `T`
strictly above `t`) sends `T.erase (max T)` bijectively onto `T.erase (min T)`.
Consequently, for every `E : ℤ → ℝ`, the sum of `E` over the successors equals the sum
of `E` over all of `T` except its minimum.
-/

/-- Unfolding of `nxtOn` when the set of elements of `T` above `t` is nonempty. -/
lemma nxtOn_eq_min' {T : Finset ℤ} {t : ℤ} (h : (T.filter (fun s => t < s)).Nonempty) :
    nxtOn T t = (T.filter (fun s => t < s)).min' h := by
  rw [nxtOn, dif_pos h]

/-- Every `t ∈ T` below the maximum of `T` has a successor in `T`. -/
lemma nxtOn_filter_nonempty' {T : Finset ℤ} (hT : T.Nonempty) {t : ℤ} (ht : t ∈ T)
    (hmax : t ≠ T.max' hT) : (T.filter (fun s => t < s)).Nonempty :=
  ⟨T.max' hT, Finset.mem_filter.mpr
    ⟨Finset.max'_mem T hT, lt_of_le_of_ne (Finset.le_max' T t ht) hmax⟩⟩

/-- The successor of `t` (when it exists) belongs to `T`. -/
lemma nxtOn_mem' {T : Finset ℤ} {t : ℤ} (h : (T.filter (fun s => t < s)).Nonempty) :
    nxtOn T t ∈ T := by
  rw [nxtOn_eq_min' h]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).1

/-- The successor of `t` is strictly larger than `t`. -/
lemma nxtOn_gt' {T : Finset ℤ} {t : ℤ} (h : (T.filter (fun s => t < s)).Nonempty) :
    t < nxtOn T t := by
  rw [nxtOn_eq_min' h]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2

/-- The successor of `t` is dominated by any element of `T` above `t`. -/
lemma nxtOn_le' {T : Finset ℤ} {t b : ℤ} (h : (T.filter (fun s => t < s)).Nonempty)
    (hb : b ∈ T) (htb : t < b) : nxtOn T t ≤ b := by
  rw [nxtOn_eq_min' h]
  exact Finset.min'_le _ b (Finset.mem_filter.mpr ⟨hb, htb⟩)

/-- The successor map lands in `T` with the minimum removed. -/
lemma nxtOn_mem_erase_min (T : Finset ℤ) (hT : T.Nonempty) :
    ∀ t ∈ T.erase (T.max' hT), nxtOn T t ∈ T.erase (T.min' hT) := by
  intro t ht
  obtain ⟨ht_ne, ht_mem⟩ := Finset.mem_erase.mp ht
  have hne := nxtOn_filter_nonempty' hT ht_mem ht_ne
  exact Finset.mem_erase.mpr
    ⟨ne_of_gt (lt_of_le_of_lt (Finset.min'_le T t ht_mem) (nxtOn_gt' hne)), nxtOn_mem' hne⟩

/-- The successor map is injective on `T` with the maximum removed. -/
lemma nxtOn_injOn (T : Finset ℤ) (hT : T.Nonempty) :
    Set.InjOn (fun t => nxtOn T t) (↑(T.erase (T.max' hT)) : Set ℤ) := by
  intro a ha b hb hab
  obtain ⟨ha_ne, ha_mem⟩ := Finset.mem_erase.mp ha
  obtain ⟨hb_ne, hb_mem⟩ := Finset.mem_erase.mp hb
  have hab' : nxtOn T a = nxtOn T b := hab
  have hna := nxtOn_filter_nonempty' hT ha_mem ha_ne
  have hnb := nxtOn_filter_nonempty' hT hb_mem hb_ne
  have hga := nxtOn_gt' hna
  have hgb := nxtOn_gt' hnb
  rcases lt_trichotomy a b with h | h | h
  · have h1 : nxtOn T a ≤ b := nxtOn_le' hna hb_mem h
    rw [hab'] at h1
    exact absurd h1 (not_le.mpr hgb)
  · exact h
  · have h1 : nxtOn T b ≤ a := nxtOn_le' hnb ha_mem h
    rw [← hab'] at h1
    exact absurd h1 (not_le.mpr hga)

/-- Every element of `T` other than its minimum is the successor of an element
of `T` other than its maximum. -/
lemma nxtOn_surj_on (T : Finset ℤ) (hT : T.Nonempty) :
    ∀ s ∈ T.erase (T.min' hT), ∃ t ∈ T.erase (T.max' hT), nxtOn T t = s := by
  intro s hs
  obtain ⟨hs_ne, hs_mem⟩ := Finset.mem_erase.mp hs
  have hmin_lt : T.min' hT < s :=
    lt_of_le_of_ne (Finset.min'_le T s hs_mem) (Ne.symm hs_ne)
  have hpre : (T.filter (fun u => u < s)).Nonempty :=
    ⟨T.min' hT, Finset.mem_filter.mpr ⟨Finset.min'_mem T hT, hmin_lt⟩⟩
  obtain ⟨ht_mem, ht_lt⟩ :=
    Finset.mem_filter.mp (Finset.max'_mem (T.filter (fun u => u < s)) hpre)
  have ht_ne : (T.filter (fun u => u < s)).max' hpre ≠ T.max' hT :=
    ne_of_lt (lt_of_lt_of_le ht_lt (Finset.le_max' T s hs_mem))
  refine ⟨(T.filter (fun u => u < s)).max' hpre, Finset.mem_erase.mpr ⟨ht_ne, ht_mem⟩, ?_⟩
  have hne : (T.filter (fun u => (T.filter (fun u => u < s)).max' hpre < u)).Nonempty :=
    ⟨s, Finset.mem_filter.mpr ⟨hs_mem, ht_lt⟩⟩
  rw [nxtOn_eq_min' hne]
  apply le_antisymm
  · exact Finset.min'_le _ s (Finset.mem_filter.mpr ⟨hs_mem, ht_lt⟩)
  · by_contra hcon
    have hlt : (T.filter (fun u => (T.filter (fun u => u < s)).max' hpre < u)).min' hne < s :=
      not_le.mp hcon
    have hmem' := Finset.min'_mem
      (T.filter (fun u => (T.filter (fun u => u < s)).max' hpre < u)) hne
    have hminT : (T.filter (fun u => (T.filter (fun u => u < s)).max' hpre < u)).min' hne ∈ T :=
      (Finset.mem_filter.mp hmem').1
    have hle : (T.filter (fun u => (T.filter (fun u => u < s)).max' hpre < u)).min' hne
        ≤ (T.filter (fun u => u < s)).max' hpre :=
      Finset.le_max' (T.filter (fun u => u < s)) _ (Finset.mem_filter.mpr ⟨hminT, hlt⟩)
    have hlt' : (T.filter (fun u => u < s)).max' hpre
        < (T.filter (fun u => (T.filter (fun u => u < s)).max' hpre < u)).min' hne :=
      (Finset.mem_filter.mp hmem').2
    exact absurd hle (not_le.mpr hlt')

/-- **Successor reindexing.** Summing `E` over the successors of the elements of `T`
below its maximum is the same as summing `E` over all of `T` except its minimum. -/
theorem nxtOn_sum_eq (T : Finset ℤ) (hT : T.Nonempty) (E : ℤ → ℝ) :
    ∑ t ∈ T.erase (T.max' hT), E (nxtOn T t) = ∑ s ∈ T.erase (T.min' hT), E s := by
  have hinj := nxtOn_injOn T hT
  have himg : (T.erase (T.max' hT)).image (fun t => nxtOn T t) = T.erase (T.min' hT) := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact nxtOn_mem_erase_min T hT t ht
    · intro s hs
      obtain ⟨t, ht, hts⟩ := nxtOn_surj_on T hT s hs
      exact Finset.mem_image.mpr ⟨t, ht, hts⟩
  have hsum := Finset.sum_image (s := T.erase (T.max' hT))
    (g := fun t => nxtOn T t) (f := E) hinj
  rw [← hsum, himg]

end Work.FIArea6b
