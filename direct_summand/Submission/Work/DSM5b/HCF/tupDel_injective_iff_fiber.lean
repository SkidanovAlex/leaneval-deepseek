import Mathlib
import Submission.Work.DSM5b.PerfComplexDefs

namespace Work.DSM5b.HCF

/-- For a surjection `v : Fin (n+2) → Fin (n+1)` and a position `i`, deleting the `i`-th entry of
`v` yields an injective tuple exactly when the fibre of `v` over `v i` has at least two elements.

Since `v` is a surjection from a set of `n+2` elements onto one of `n+1` elements, exactly one fibre
has two elements and all others have one; `tupDel i v = v ∘ Fin.succAbove i` is injective iff `v` is
injective away from `i`, which happens exactly when `v i` is attained somewhere other than at `i`. -/
theorem tupDel_injective_iff_fiber {n : ℕ} (v : Fin (n + 2) → Fin (n + 1))
    (hv : Function.Surjective v) (i : Fin (n + 2)) :
    Function.Injective (Work.DSM5b.tupDel i v) ↔
      2 ≤ (Finset.univ.filter (fun c : Fin (n + 2) => v c = v i)).card := by
  classical
  -- `T` is the image of `v` on the complement of `i`; `s` is the fibre of `v i`.
  set T : Finset (Fin (n + 1)) := (Finset.univ.filter (fun c : Fin (n + 2) => c ≠ i)).image v
    with hT
  set s : Finset (Fin (n + 2)) := Finset.univ.filter (fun c : Fin (n + 2) => v c = v i)
    with hs
  have hi_mem : i ∈ s := by
    rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  -- The image of the truncated tuple is `T`.
  have himg : Finset.univ.image (Work.DSM5b.tupDel i v) = T := by
    ext x
    rw [hT]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨Fin.succAbove i b, by simp, hb⟩
    · rintro ⟨c, hcne, hcv⟩
      obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hcne
      exact ⟨b, by rw [Work.DSM5b.tupDel_apply, hb]; exact hcv⟩
  -- `v` is surjective, so `v` attains every value.
  have huniv : Finset.univ.image v = (Finset.univ : Finset (Fin (n + 1))) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => hv x⟩
  -- `T` together with `v i` covers everything.
  have hunionT : T ∪ {v i} = (Finset.univ : Finset (Fin (n + 1))) := by
    have h : T ∪ {v i} = Finset.univ.image v := by
      ext x
      rw [hT]
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro (⟨c, _, hcv⟩ | hx)
        · exact ⟨c, hcv⟩
        · exact ⟨i, hx.symm⟩
      · rintro ⟨c, hcv⟩
        by_cases hci : c = i
        · exact Or.inr (by rw [hci] at hcv; exact hcv.symm)
        · exact Or.inl ⟨c, hci, hcv⟩
    rw [h, huniv]
  -- Cardinality criterion for injectivity of a self-map of a finite set.
  have h1 : Function.Injective (Work.DSM5b.tupDel i v) ↔
      (Finset.univ.image (Work.DSM5b.tupDel i v)).card =
        (Finset.univ : Finset (Fin (n + 1))).card := by
    constructor
    · intro hinj
      exact Finset.card_image_of_injective _ hinj
    · intro hcard
      rw [Finset.card_image_iff] at hcard
      rw [Finset.coe_univ, Set.injOn_univ] at hcard
      exact hcard
  have h2 : Finset.univ.image (Work.DSM5b.tupDel i v) = (Finset.univ : Finset (Fin (n + 1))) ↔
      (Finset.univ.image (Work.DSM5b.tupDel i v)).card =
        (Finset.univ : Finset (Fin (n + 1))).card := by
    constructor
    · intro h
      rw [h]
    · intro h
      exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (le_of_eq h.symm)
  have hmain : Function.Injective (Work.DSM5b.tupDel i v) ↔ v i ∈ T := by
    rw [h1, ← h2, himg]
    constructor
    · intro hT
      rw [hT]
      exact Finset.mem_univ _
    · intro hvT
      have hTT : T = T ∪ {v i} :=
        ((Finset.union_eq_left).mpr (Finset.singleton_subset_iff.mpr hvT)).symm
      exact hTT.trans hunionT
  -- `v i ∈ T` iff `v i` has another preimage, which is exactly `2 ≤ card s`.
  have hcard : (2 ≤ s.card) ↔ ∃ c : Fin (n + 2), c ≠ i ∧ v c = v i := by
    constructor
    · intro h2
      by_contra hcon
      have hsub : s ⊆ {i} := by
        intro c hc
        rw [Finset.mem_singleton]
        by_contra hci
        rw [hs, Finset.mem_filter] at hc
        exact hcon ⟨c, hci, hc.2⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hle
      omega
    · rintro ⟨c, hcne, hcv⟩
      have hc : c ∈ s := by
        rw [hs, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hcv⟩
      have hsub : ({i, c} : Finset (Fin (n + 2))) ⊆ s := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi_mem
        · rw [Finset.mem_singleton] at hx
          rw [hx]
          exact hc
      have hle := Finset.card_le_card hsub
      have h2 : ({i, c} : Finset (Fin (n + 2))).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa [Finset.mem_singleton] using hcne.symm),
          Finset.card_singleton]
      omega
  have hd : v i ∈ T ↔ 2 ≤ s.card := by
    have hmem : v i ∈ T ↔ ∃ c : Fin (n + 2), c ≠ i ∧ v c = v i := by
      rw [hT]
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmem.trans hcard.symm
  exact hmain.trans hd

end Work.DSM5b.HCF
