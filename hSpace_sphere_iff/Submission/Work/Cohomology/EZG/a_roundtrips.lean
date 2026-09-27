/-
# The `a`-side reindexing map of the Eilenberg–Zilber shuffle lemma is a bijection

The `a`-side of the expanded boundary of the shuffle chain is indexed by `IdxA P Q` (shuffles of
`(P+1,Q+1)`-type together with a face index satisfying `IsA`), and `aFwd` reindexes it by
`TargetA P Q` (shuffles of `(P,Q+1)`-type together with the index `i = cnt A k` of the deleted
`a`-letter).  `aInvIdx` is the inverse operation, inserting an `a`-letter at the position
determined by `i`.  This file proves that the two are mutually inverse:
`Work.Cohomology.EZG.a_roundtrips`.

The combinatorics is packaged in two generic lemmas about `Finset.orderEmbOfFin`
(`cnt_orderEmbOfFin` and its converse `orderEmbOfFin_of_cnt`) and the insertion/deletion lemmas
`cnt_insUp_self`, `cnt_delPosP_of_le` and the key `orderEmbOfFin_delPosP_pred`.
-/
import Mathlib
import Submission.Work.Cohomology.EZG.EZShufSetup

namespace Work.Cohomology.EZG

noncomputable section

/-! ## Generic counting lemmas for `orderEmbOfFin` -/

/-- The number of elements of `s` strictly below its `j`-th element is `j`. -/
lemma cnt_orderEmbOfFin {n k : ℕ} (s : Finset (Fin n)) (h : s.card = k) (j : Fin k) :
    cnt s ((s.orderEmbOfFin h j).val) = j.val := by
  rw [cnt]
  have hset : s.filter (fun x : Fin n => x.val < (s.orderEmbOfFin h j).val)
      = ((Finset.univ : Finset (Fin k)).filter (fun i => i.val < j.val)).image
          (s.orderEmbOfFin h) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxs, hxj⟩
      have hx : x ∈ Finset.image (s.orderEmbOfFin h) (Finset.univ : Finset (Fin k)) := by
        rwa [Finset.image_orderEmbOfFin_univ]
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hx
      refine ⟨i, ?_, hi⟩
      have hlt : s.orderEmbOfFin h i < s.orderEmbOfFin h j := by rw [hi]; exact Fin.lt_def.mpr hxj
      exact Fin.lt_def.mp ((s.orderEmbOfFin h).lt_iff_lt.mp hlt)
    · rintro ⟨i, hij, hi⟩
      subst hi
      exact ⟨s.orderEmbOfFin_mem h i,
        Fin.lt_def.mp ((s.orderEmbOfFin h).lt_iff_lt.mpr (Fin.lt_def.mpr hij))⟩
  rw [hset, Finset.card_image_of_injective _ (s.orderEmbOfFin h).injective,
      card_filter_lt (le_of_lt j.isLt)]

/-- The number of elements of `s` that are `≤` its `j`-th element is `j+1`. -/
lemma cnt_succ_orderEmbOfFin {n k : ℕ} (s : Finset (Fin n)) (h : s.card = k) (j : Fin k) :
    cnt s ((s.orderEmbOfFin h j).val + 1) = j.val + 1 := by
  rw [cnt_succ_of_mem s (m := (s.orderEmbOfFin h j).val)
      (s.orderEmbOfFin h j).isLt (s.orderEmbOfFin_mem h j), cnt_orderEmbOfFin s h j]

/-- Converse of `cnt_succ_orderEmbOfFin`: an element `t ∈ s` that bounds exactly `j+1` elements of
`s` from below is the `j`-th element of `s`. -/
lemma orderEmbOfFin_of_cnt {n k : ℕ} (s : Finset (Fin n)) (h : s.card = k)
    {t : Fin n} (ht : t ∈ s) {j : ℕ} (hj : j < k)
    (hc : cnt s (t.val + 1) = j + 1) : s.orderEmbOfFin h ⟨j, hj⟩ = t := by
  set i := (s.orderIsoOfFin h).symm ⟨t, ht⟩ with hi
  have hcoef : (s.orderEmbOfFin h i : Fin n) = t := by
    rw [← Finset.coe_orderIsoOfFin_apply, hi]
    exact congrArg Subtype.val (OrderIso.apply_symm_apply _ _)
  have hval : i.val = j := by
    have h1 : cnt s ((s.orderEmbOfFin h i).val + 1) = i.val + 1 :=
      cnt_succ_orderEmbOfFin s h i
    rw [hcoef] at h1
    omega
  rw [show (⟨j, hj⟩ : Fin k) = i from Fin.ext hval.symm, hcoef]

/-! ## Helper lemmas for the `a`-side roundtrip -/

/-- Inserting a position does not change `cnt` below that position. -/
lemma cnt_insUp_self {N : ℕ} (A' : Finset (Fin N)) (p : Fin (N+1)) :
    cnt (insUp A' p) p.val = cnt A' p.val := by
  rw [cnt, cnt]
  have hset : (insUp A' p).filter (fun x : Fin (N+1) => x.val < p.val)
      = (A'.filter (fun t : Fin N => t.val < p.val)).image (Fin.succAbove p) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hx, hlt⟩
      rw [mem_insUp] at hx
      rcases hx with rfl | ⟨t, ht, rfl⟩
      · exact absurd hlt (lt_irrefl _)
      · refine ⟨t, ⟨ht, ?_⟩, rfl⟩
        rw [val_succAbove_aux] at hlt
        by_cases h : t.val < p.val
        · exact h
        · rw [if_neg h] at hlt; omega
    · rintro ⟨t, ⟨ht, hlt⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [mem_insUp]; exact Or.inr ⟨t, ht, rfl⟩
      · rw [val_succAbove_aux, if_pos hlt]; exact hlt
  rw [hset, Finset.card_image_of_injective _ Fin.succAbove_right_injective]

/-- Deleting a position does not change `cnt` below that position. -/
lemma cnt_delPosP_of_le {N : ℕ} (A : Finset (Fin (N+1))) (p : Fin (N+1)) {m : ℕ}
    (hm : m ≤ p.val) : cnt (delPosP A p) m = cnt A m := by
  rw [cnt, cnt]
  have hset : A.filter (fun i : Fin (N+1) => i.val < m)
      = ((delPosP A p).filter (fun t : Fin N => t.val < m)).image (Fin.succAbove p) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hiA, him⟩
      have hne : i ≠ p := by rintro rfl; omega
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hne
      refine ⟨t, ⟨?_, ?_⟩, ht⟩
      · rw [mem_delPosP, ht]; exact hiA
      · rw [← ht] at him
        rw [val_succAbove_aux] at him
        by_cases h : t.val < p.val
        · rw [if_pos h] at him; exact him
        · rw [if_neg h] at him; omega
    · rintro ⟨t, ⟨ht, htm⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rwa [mem_delPosP] at ht
      · rw [val_succAbove_aux, if_pos (by omega)]; exact htm
  rw [hset, Finset.card_image_of_injective _ Fin.succAbove_right_injective]

/-- An element of `A` is not counted by `cnt A` at its own value. -/
lemma cnt_le_card_sub_one {N : ℕ} (A : Finset (Fin (N+1))) (p : Fin (N+1)) (hp : p ∈ A) :
    cnt A p.val ≤ A.card - 1 := by
  rw [cnt, ← Finset.card_erase_of_mem hp]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx
  rw [Finset.mem_erase]
  exact ⟨fun h => by rw [h] at hx; exact lt_irrefl _ hx.2, hx.1⟩

/-- The Key lemma: for `q.castSucc ∈ A` with `q.val + 1 = p.val`, the `j`-th element of
`delPosP A p` is `q`, where `j = cnt A p.val - 1`. -/
lemma orderEmbOfFin_delPosP_pred {N : ℕ} {A : Finset (Fin (N+1))} {p : Fin (N+1)} {q : Fin N}
    (hq : q.castSucc ∈ A) (hqv : q.val + 1 = p.val)
    {k : ℕ} (h : (delPosP A p).card = k) {j : ℕ} (hj : j < k)
    (hjv : j = cnt A p.val - 1) :
    (delPosP A p).orderEmbOfFin h ⟨j, hj⟩ = q := by
  have hqlt : q.val < p.val := by omega
  have hmq : q ∈ delPosP A p := by
    rw [mem_delPosP, Fin.succAbove_of_castSucc_lt p q (by rw [Fin.lt_def, Fin.val_castSucc]; exact hqlt)]
    exact hq
  have h1 : cnt (delPosP A p) p.val = cnt A p.val := cnt_delPosP_of_le A p (le_refl p.val)
  have hpos : 1 ≤ cnt A p.val := by
    rw [cnt]
    exact Finset.card_pos.mpr ⟨q.castSucc,
      Finset.mem_filter.mpr ⟨hq, by rw [Fin.val_castSucc]; omega⟩⟩
  have hc : cnt (delPosP A p) (q.val + 1) = j + 1 := by
    rw [hqv, h1, hjv]; omega
  exact orderEmbOfFin_of_cnt (delPosP A p) h hmq hj hc

theorem a_roundtrips (P Q : ℕ) :
    (∀ y : TargetA P Q, IsA ((P+1)+Q) (aInvIdx P Q y).1.1 (aInvIdx P Q y).2) ∧
    (∀ (y : TargetA P Q) (h : IsA ((P+1)+Q) (aInvIdx P Q y).1.1 (aInvIdx P Q y).2),
        aFwd P Q ⟨aInvIdx P Q y, h⟩ = y) ∧
    (∀ (x : Idx P Q) (h : IsA ((P+1)+Q) x.1.1 x.2),
        aInvIdx P Q (aFwd P Q ⟨x, h⟩) = x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [aInvIdx]
    split_ifs with h0 hl
    · refine ⟨?_, Or.inl rfl⟩
      have hd0 : delIdx (0 : Fin ((P+1)+Q+2)) = (0 : Fin ((P+1)+Q+1)) := by
        ext; rw [delIdx_val]; exact Nat.zero_min _
      rw [hd0, mem_insUp]; exact Or.inl rfl
    · refine ⟨?_, Or.inr (Or.inl (by rw [Fin.val_last]))⟩
      have hd1 : delIdx (Fin.last ((P+1)+Q+1)) = Fin.last ((P+1)+Q) := by
        ext; rw [delIdx_val, Fin.val_last, Fin.val_last]; exact Nat.min_eq_right (Nat.le_succ _)
      rw [hd1, mem_insUp]; exact Or.inl rfl
    · set b := y.1.1.orderEmbOfFin y.1.2 ⟨y.2.val - 1, by omega⟩ with hb
      refine ⟨?_, Or.inr (Or.inr ?_)⟩
      · have htd : delIdx (Fin.succ (Fin.castSucc b)) = Fin.succ b := by
          apply Fin.ext
          rw [delIdx_val]
          have h1 : (Fin.succ (Fin.castSucc b)).val = b.val + 1 := rfl
          have h2 : (Fin.succ b).val = b.val + 1 := rfl
          rw [h1, h2]
          exact Nat.min_eq_left (by have := b.isLt; omega)
        rw [htd, mem_insUp]; exact Or.inl rfl
      · rw [mem_insUp]; right
        refine ⟨b, y.1.1.orderEmbOfFin_mem y.1.2 _, ?_⟩
        rw [Fin.succAbove_of_castSucc_lt (Fin.succ b) b
          (by rw [Fin.lt_def, Fin.val_castSucc]; exact Nat.lt_succ_self b.val)]
        apply Fin.ext
        show b.val = (Fin.succ (Fin.castSucc b)).val - 1
        have h1 : (Fin.succ (Fin.castSucc b)).val = b.val + 1 := rfl
        rw [h1]
        omega
  · intro y h
    by_cases h0 : y.2.val = 0
    · have hfst : (aInvIdx P Q y).1.1 = insUp y.1.1 0 := by
        rw [aInvIdx]; simp only [dif_pos h0]
      have hsnd : (aInvIdx P Q y).2 = 0 := by
        rw [aInvIdx]; simp only [dif_pos h0]
      apply Prod.ext
      · apply Subtype.ext
        show delPosP (aInvIdx P Q y).1.1 (delIdx (aInvIdx P Q y).2) = y.1.1
        have hd0 : delIdx (0 : Fin ((P+1)+Q+2)) = (0 : Fin ((P+1)+Q+1)) := by
          ext; rw [delIdx_val]; exact Nat.zero_min _
        rw [hfst, hsnd, hd0, delPosP_insUp]
      · apply Fin.ext
        show cnt (aInvIdx P Q y).1.1 (aInvIdx P Q y).2.val = y.2.val
        have hc : cnt (insUp y.1.1 0) ((0 : Fin ((P+1)+Q+2))).val = 0 := by rw [cnt]; simp
        rw [hfst, hsnd, hc, h0]
    · by_cases hl : y.2.val = P+1
      · have hfst : (aInvIdx P Q y).1.1 = insUp y.1.1 (Fin.last ((P+1)+Q)) := by
          rw [aInvIdx]; simp only [dif_neg h0, dif_pos hl]
        have hsnd : (aInvIdx P Q y).2 = Fin.last ((P+1)+Q+1) := by
          rw [aInvIdx]; simp only [dif_neg h0, dif_pos hl]
        apply Prod.ext
        · apply Subtype.ext
          show delPosP (aInvIdx P Q y).1.1 (delIdx (aInvIdx P Q y).2) = y.1.1
          have hd1 : delIdx (Fin.last ((P+1)+Q+1)) = Fin.last ((P+1)+Q) := by
            ext; rw [delIdx_val, Fin.val_last, Fin.val_last]; exact Nat.min_eq_right (Nat.le_succ _)
          rw [hfst, hsnd, hd1, delPosP_insUp]
        · apply Fin.ext
          show cnt (aInvIdx P Q y).1.1 (aInvIdx P Q y).2.val = y.2.val
          have hc : cnt (insUp y.1.1 (Fin.last ((P+1)+Q)))
              (Fin.last ((P+1)+Q+1)).val = y.2.val := by
            rw [show (Fin.last ((P+1)+Q+1)).val = (P+1)+Q+1 from rfl]
            rw [cnt_eq_card (insUp y.1.1 (Fin.last ((P+1)+Q))) (le_refl ((P+1)+Q+1)), insUp_card,
              y.1.2, hl]
          rw [hfst, hsnd, hc]
      · have hfst : (aInvIdx P Q y).1.1
            = insUp y.1.1 (Fin.succ (y.1.1.orderEmbOfFin y.1.2 ⟨y.2.val - 1, by omega⟩)) := by
          rw [aInvIdx]; simp only [dif_neg h0, dif_neg hl]
        have hsnd : (aInvIdx P Q y).2
            = Fin.succ (Fin.castSucc (y.1.1.orderEmbOfFin y.1.2 ⟨y.2.val - 1, by omega⟩)) := by
          rw [aInvIdx]; simp only [dif_neg h0, dif_neg hl]
        apply Prod.ext
        · apply Subtype.ext
          show delPosP (aInvIdx P Q y).1.1 (delIdx (aInvIdx P Q y).2) = y.1.1
          rw [hfst, hsnd]
          set b := y.1.1.orderEmbOfFin y.1.2 ⟨y.2.val - 1, by omega⟩ with hb
          have htd : delIdx (Fin.succ (Fin.castSucc b)) = Fin.succ b := by
            apply Fin.ext
            rw [delIdx_val]
            have h1 : (Fin.succ (Fin.castSucc b)).val = b.val + 1 := rfl
            have h2 : (Fin.succ b).val = b.val + 1 := rfl
            rw [h1, h2]
            exact Nat.min_eq_left (by have := b.isLt; omega)
          rw [htd, delPosP_insUp]
        · apply Fin.ext
          show cnt (aInvIdx P Q y).1.1 (aInvIdx P Q y).2.val = y.2.val
          rw [hfst, hsnd]
          set b := y.1.1.orderEmbOfFin y.1.2 ⟨y.2.val - 1, by omega⟩ with hb
          have hc : cnt (insUp y.1.1 (Fin.succ b)) (Fin.succ (Fin.castSucc b)).val = y.2.val := by
            rw [show (Fin.succ (Fin.castSucc b)).val = (Fin.succ b).val from rfl, cnt_insUp_self]
            rw [show (Fin.succ b).val = b.val + 1 from rfl]
            have h4 := cnt_succ_orderEmbOfFin y.1.1 y.1.2 ⟨y.2.val - 1, by omega⟩
            rw [← hb] at h4
            rw [h4]
            show y.2.val - 1 + 1 = y.2.val
            omega
          exact hc
  · intro x h
    obtain ⟨⟨A, hA⟩, k⟩ := x
    have hI : delIdx k ∈ A := h.1
    have hD : k.val = 0 ∨ k.val = (P+1)+Q+1 ∨
        (⟨k.val - 1, by omega⟩ : Fin ((P+1)+Q+1)) ∈ A := h.2
    have hy : aFwd P Q ⟨(⟨A, hA⟩, k), h⟩
        = (⟨delPosP A (delIdx k), by rw [delPosP_card hI, hA]; omega⟩,
           ⟨cnt A k.val, by have := cnt_le_card A k.val; omega⟩) := rfl
    rw [hy]
    set i := cnt A k.val with hi
    rw [aInvIdx]
    split_ifs with hi0 hiP
    · -- first branch: i = 0
      have hi0' : i = 0 := hi0
      have hk0 : k.val = 0 := by
        by_contra hne
        rcases hD with h1 | h1 | h1
        · exact hne h1
        · have hicard : i = A.card := by rw [hi, h1]; exact cnt_eq_card A (le_refl _)
          omega
        · have hmem : (⟨k.val - 1, by omega⟩ : Fin ((P+1)+Q+1))
              ∈ A.filter (fun x => x.val < k.val) := by
            rw [Finset.mem_filter]
            exact ⟨h1, by rw [Fin.val_mk]; omega⟩
          have hpos : 1 ≤ cnt A k.val := by
            rw [cnt]; exact Finset.card_pos.mpr ⟨_, hmem⟩
          omega
      have hd : delIdx k = (0 : Fin ((P+1)+Q+1)) := by
        apply Fin.ext
        rw [delIdx_val, hk0]; simp
      apply Prod.ext
      · apply Subtype.ext
        show insUp (delPosP A (delIdx k)) (0 : Fin ((P+1)+Q+1)) = A
        rw [hd]
        exact insUp_delPosP (p := (0 : Fin ((P+1)+Q+1))) (by rw [← hd]; exact hI)
      · show (0 : Fin ((P+1)+Q+2)) = k
        apply Fin.ext
        rw [hk0]
        rfl
    · -- second branch: i = P+1
      have hiP' : i = P+1 := hiP
      have hk : k.val = (P+1)+Q+1 := by
        by_contra hne
        have hle : k.val ≤ (P+1)+Q := by omega
        have hd : delIdx k = ⟨k.val, Nat.lt_succ_of_le hle⟩ := delIdx_of_le k hle
        have hmem : (⟨k.val, Nat.lt_succ_of_le hle⟩ : Fin ((P+1)+Q+1)) ∈ A := by
          rw [← hd]; exact hI
        have hle2 : cnt A k.val ≤ A.card - 1 :=
          cnt_le_card_sub_one A ⟨k.val, Nat.lt_succ_of_le hle⟩ hmem
        omega
      have hd : delIdx k = Fin.last ((P+1)+Q) := by
        apply Fin.ext
        rw [delIdx_val, hk]
        show Nat.min ((P+1)+Q+1) ((P+1)+Q) = ((P+1)+Q)
        exact Nat.min_eq_right (Nat.le_succ _)
      apply Prod.ext
      · apply Subtype.ext
        show insUp (delPosP A (delIdx k)) (Fin.last ((P+1)+Q)) = A
        rw [hd]
        exact insUp_delPosP (p := Fin.last ((P+1)+Q)) (by rw [← hd]; exact hI)
      · show Fin.last ((P+1)+Q+1) = k
        apply Fin.ext
        rw [hk]
        rfl
    · -- third branch
      have hi0' : i ≠ 0 := hi0
      have hiP' : i ≠ P+1 := hiP
      have hkne : k.val ≠ (P+1)+Q+1 := by
        intro hk
        have hicard : i = A.card := by rw [hi, hk]; exact cnt_eq_card A (le_refl _)
        exact hiP' (hicard.trans hA)
      have hle : k.val ≤ (P+1)+Q := by omega
      have hkge : 1 ≤ k.val := by
        rcases Nat.eq_zero_or_pos k.val with h0 | h0
        · exfalso
          have hone : i = 0 := by rw [hi, h0]; simp [cnt]
          exact hi0' hone
        · exact h0
      have hprev : (⟨k.val - 1, by omega⟩ : Fin ((P+1)+Q+1)) ∈ A := by
        rcases hD with h1 | h1 | h1
        · omega
        · omega
        · exact h1
      have hp : delIdx k = ⟨k.val, Nat.lt_succ_of_le hle⟩ := delIdx_of_le k hle
      set q : Fin ((P+1)+Q) := ⟨k.val - 1, by omega⟩ with hq
      have hqcast : q.castSucc ∈ A := hprev
      have hqv : q.val + 1 = (delIdx k).val := by
        rw [hp]; show k.val - 1 + 1 = k.val; omega
      have hik : i = cnt A (delIdx k).val := by rw [hi, hp]
      have hile : i ≤ P := by
        have hc := cnt_le_card_sub_one A (delIdx k) hI
        omega
      have hilt : i - 1 < P := by omega
      have hjv : i - 1 = cnt A (delIdx k).val - 1 := by rw [hik]
      have key := orderEmbOfFin_delPosP_pred (A := A) (p := delIdx k) (q := q)
        hqcast hqv (k := P) (by rw [delPosP_card hI, hA]; omega) hilt hjv
      apply Prod.ext
      · apply Subtype.ext
        show insUp (delPosP A (delIdx k))
            (Fin.succ ((delPosP A (delIdx k)).orderEmbOfFin
              (by rw [delPosP_card hI, hA]; omega) ⟨i - 1, hilt⟩)) = A
        rw [key]
        have hsucc : Fin.succ q = delIdx k := by
          apply Fin.ext
          rw [hp]
          show q.val + 1 = k.val
          rw [hq]; show k.val - 1 + 1 = k.val; omega
        rw [hsucc]
        exact insUp_delPosP (p := delIdx k) hI
      · show Fin.succ (Fin.castSucc ((delPosP A (delIdx k)).orderEmbOfFin
            (by rw [delPosP_card hI, hA]; omega) ⟨i - 1, hilt⟩)) = k
        rw [key]
        have hv : (Fin.succ (Fin.castSucc q)).val = q.val + 1 := rfl
        apply Fin.ext
        rw [hv, hq]
        show k.val - 1 + 1 = k.val
        omega
end

end Work.Cohomology.EZG
