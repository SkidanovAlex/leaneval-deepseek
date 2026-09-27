/-
The two round trips for the `b`-side reindexing of the expanded boundary of the
Eilenberg–Zilber shuffle chain: `bInvIdx` inserts the `b`-letter determined by the face
index `j` and `bFwd` records the deleted position together with the number of `b`-letters
below it; the two maps are mutually inverse on the appropriate domains.
-/
import Mathlib
import Submission.Work.Cohomology.EZG.EZShufSetup


namespace Work.Cohomology.EZG

noncomputable section

open CategoryTheory Simplicial Opposite

/-- Deleting the position `p` from `A` and then shifting the result up at `p` returns `A`,
when `p ∉ A`. -/
lemma shUp_delPosP_of_notMem {n : ℕ} (A : Finset (Fin (n+1))) (p : Fin (n+1)) (hp : p ∉ A) :
    shUp (delPosP A p) p = A := by
  rw [shUp]
  exact image_succAbove_delPosP A p hp

/-- `cntB (shUp A p) m = cntB A m` for thresholds `m ≤ p.val`. -/
lemma cntB_shUp_of_le {n : ℕ} (A : Finset (Fin n)) (p : Fin (n+1)) {m : ℕ} (hm : m ≤ p.val) :
    cntB (shUp A p) m = cntB A m := by
  rw [cntB, cntB]
  have hset : (Finset.univ \ shUp A p).filter (fun u : Fin (n+1) => u.val < m)
      = ((Finset.univ \ A).filter (fun t : Fin n => t.val < m)).image (Fin.succAbove p) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro ⟨huB, hum⟩
      have hup : u ≠ p := fun h => by rw [h] at hum; omega
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hup
      refine ⟨t, ⟨?_, ?_⟩, ht⟩
      · intro htA
        exact huB (by rw [← ht, shUp, Finset.mem_image]; exact ⟨t, htA, rfl⟩)
      · have hle : t.val ≤ (Fin.succAbove p t).val := by
          rw [Work.Cohomology.EZG.val_succAbove_aux]; split <;> omega
        rw [ht] at hle; omega
    · rintro ⟨t, ⟨htB, htm⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · intro hmem
        rw [shUp, Finset.mem_image] at hmem
        obtain ⟨t', ht', h'⟩ := hmem
        rw [Fin.succAbove_right_injective h'] at ht'
        exact htB ht'
      · have hvp : t.val < p.val := lt_of_lt_of_le htm hm
        rw [Work.Cohomology.EZG.val_succAbove_aux, if_pos hvp]
        exact htm
  rw [hset, Finset.card_image_of_injective _ (Fin.succAbove_right_injective (p := p))]

end

end Work.Cohomology.EZG

namespace Work.Cohomology.EZG

noncomputable section

open CategoryTheory Simplicial Opposite

/-- Rank lemma: the number of elements of `s` below `s.orderEmbOfFin h i` is `i.val`. -/
lemma card_filter_lt_orderEmbOfFin {α : Type*} [LinearOrder α]
    (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    (s.filter (fun y => y < s.orderEmbOfFin h i)).card = i.val := by
  classical
  have key : (Finset.Iio i : Finset (Fin k)).card
      = (s.filter (fun y => y < s.orderEmbOfFin h i)).card := by
    refine Finset.card_bij (fun (j : Fin k) (_ : j ∈ Finset.Iio i) => s.orderEmbOfFin h j)
      ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_Iio] at hj
      rw [Finset.mem_filter]
      exact ⟨Finset.orderEmbOfFin_mem s h j,
        (s.orderEmbOfFin h).lt_iff_lt.mpr hj⟩
    · intro j1 _ j2 _ hh
      exact (s.orderEmbOfFin h).injective hh
    · intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨hyS, hyi⟩ := hy
      obtain ⟨j, hj⟩ := Set.mem_range.mp (show y ∈ Set.range (s.orderEmbOfFin h) from by
        rw [Finset.range_orderEmbOfFin]; exact hyS)
      refine ⟨j, ?_, hj⟩
      rw [Finset.mem_Iio]
      exact (s.orderEmbOfFin h).lt_iff_lt.mp (by rw [hj]; exact hyi)
  rw [← key]
  exact Fin.card_Iio i

/-- Rank lemma, `.val` form. -/
lemma card_filter_val_lt_orderEmbOfFin {M : ℕ} (s : Finset (Fin M)) {Q : ℕ}
    (h : s.card = Q) (i : Fin Q) :
    (s.filter (fun y => y.val < (s.orderEmbOfFin h i).val)).card = i.val := by
  rw [show (s.filter (fun y => y.val < (s.orderEmbOfFin h i).val))
      = (s.filter (fun y => y < s.orderEmbOfFin h i)) from ?_]
  · exact card_filter_lt_orderEmbOfFin s h i
  · ext y
    simp only [Finset.mem_filter]
    constructor <;> intro hh <;> exact ⟨hh.1, Fin.lt_def.mpr hh.2⟩

/-- `cntB` at `t.val+1` for `t ∉ A`. -/
lemma cntB_succ_of_notMem {n : ℕ} (A : Finset (Fin n)) {t : Fin n} (ht : t ∉ A) :
    cntB A (t.val + 1) = cntB A t.val + 1 := by
  rw [cntB, cntB]
  have hf : (Finset.univ \ A).filter (fun i : Fin n => i.val < t.val + 1) =
      (Finset.univ \ A).filter (fun i : Fin n => i.val < t.val) ∪ {t} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hiA, hi⟩
      by_cases h : i = t
      · exact Or.inr h
      · left; exact ⟨hiA, by omega⟩
    · rintro (⟨hiA, hi⟩ | rfl)
      · exact ⟨hiA, by omega⟩
      · exact ⟨ht, by omega⟩
  have hdisj : Disjoint ((Finset.univ \ A).filter (fun i : Fin n => i.val < t.val))
      ({t} : Finset (Fin n)) := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_filter, not_and]
    intro _ h; omega
  rw [hf, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]

/-- Value characterization of `orderEmbOfFin`: an element of `s` with `i.val` elements below it. -/
lemma orderEmbOfFin_eq_of_card_filter_val_lt {M : ℕ} (s : Finset (Fin M)) {Q : ℕ}
    (h : s.card = Q) {x : Fin M} (hx : x ∈ s) {i : Fin Q}
    (hi : (s.filter (fun y => y.val < x.val)).card = i.val) :
    s.orderEmbOfFin h i = x := by
  set c := s.orderEmbOfFin h i with hc
  have hcmem : c ∈ s := Finset.orderEmbOfFin_mem s h i
  have hcrank : (s.filter (fun y => y.val < c.val)).card = i.val :=
    card_filter_val_lt_orderEmbOfFin s h i
  rcases lt_trichotomy c x with hlt | heq | hgt
  · have hss : (s.filter (fun y => y.val < c.val)).card
        < (s.filter (fun y => y.val < x.val)).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro y hy
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, by omega⟩
      · intro hcon
        have : c ∈ s.filter (fun y => y.val < x.val) := Finset.mem_filter.mpr ⟨hcmem, hlt⟩
        rw [← hcon] at this
        simp only [Finset.mem_filter] at this; omega
    omega
  · exact heq
  · have hss : (s.filter (fun y => y.val < x.val)).card
        < (s.filter (fun y => y.val < c.val)).card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro y hy
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨hy.1, by omega⟩
      · intro hcon
        have : x ∈ s.filter (fun y => y.val < c.val) := Finset.mem_filter.mpr ⟨hx, hgt⟩
        rw [← hcon] at this
        simp only [Finset.mem_filter] at this; omega
    omega

end

end Work.Cohomology.EZG

namespace Work.Cohomology.EZG

noncomputable section

open CategoryTheory Simplicial Opposite

lemma succAbove_eq_of_lt {N : ℕ} (p : Fin (N+1)) (t : Fin N) (h : t.val < p.val) :
    Fin.succAbove p t = t.castSucc :=
  Fin.succAbove_of_castSucc_lt p t (by simp only [Fin.lt_def, Fin.val_castSucc]; exact h)

lemma succAbove_val_of_lt {N : ℕ} (p : Fin (N+1)) (t : Fin N) (h : t.val < p.val) :
    (Fin.succAbove p t).val = t.val := by
  rw [succAbove_eq_of_lt p t h, Fin.val_castSucc]

/-- Counting the complement of `delPosP A p` below `p.val - 1`. -/
lemma card_filter_lt_comp_delPosP {N : ℕ} (A : Finset (Fin (N+1))) (p : Fin (N+1))
    (hp : p ∉ A) (hp1 : 1 ≤ p.val) (he : (⟨p.val - 1, by omega⟩ : Fin (N+1)) ∉ A) :
    ((Finset.univ \ delPosP A p).filter (fun t : Fin N => t.val < p.val - 1)).card
      = cntB A p.val - 1 := by
  have hsucc : cntB A p.val = cntB A (p.val - 1) + 1 := by
    have h := cntB_succ_of_notMem A he
    have hv : (⟨p.val - 1, by omega⟩ : Fin (N+1)).val + 1 = p.val := by
      simp only [Fin.val_mk]; omega
    rwa [hv] at h
  have hcard2 : ((Finset.univ \ delPosP A p).filter (fun t : Fin N => t.val < p.val - 1)).card
      = cntB A (p.val - 1) := by
    have himg : ((Finset.univ \ delPosP A p).filter (fun t : Fin N => t.val < p.val - 1)).image
        (Fin.succAbove p)
        = (Finset.univ \ A).filter (fun b : Fin (N+1) => b.val < p.val - 1) := by
      ext b
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨t, ⟨htB, htlt⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · intro hmem
          exact htB (mem_delPosP.mpr hmem)
        · rw [succAbove_val_of_lt p t (show t.val < p.val by omega)]
          exact htlt
      · rintro ⟨hbA, hblt⟩
        set t : Fin N := ⟨b.val, by omega⟩ with ht
        have htval : t.val = b.val := by simp [ht]
        have htlt : t.val < p.val := by omega
        have hsuccb : Fin.succAbove p t = b := by
          rw [succAbove_eq_of_lt p t htlt]
          exact Fin.ext (by rw [Fin.val_castSucc, htval])
        have htmem : t ∉ delPosP A p := by
          intro hmem; rw [mem_delPosP, hsuccb] at hmem; exact hbA hmem
        exact ⟨t, ⟨htmem, by omega⟩, hsuccb⟩
    have h1 : ((Finset.univ \ delPosP A p).filter
          (fun t : Fin N => t.val < p.val - 1)).card
        = ((Finset.univ \ A).filter (fun b : Fin (N+1) => b.val < p.val - 1)).card := by
      rw [← himg, Finset.card_image_of_injective _ (Fin.succAbove_right_injective (p := p))]
    rw [h1]
    rfl
  omega

/-- `cntB` of a shuffle at the order statistic of its complement, plus one. -/
lemma cntB_orderEmb_compl {M : ℕ} (A : Finset (Fin M)) {Q : ℕ}
    (hcard : (Finset.univ \ A).card = Q) (i : Fin Q) :
    cntB A (((Finset.univ \ A).orderEmbOfFin hcard i).val + 1) = i.val + 1 := by
  set c := (Finset.univ \ A).orderEmbOfFin hcard i with hc
  have hcmem : c ∈ Finset.univ \ A := by
    rw [hc]; exact Finset.orderEmbOfFin_mem _ hcard i
  have hrank : ((Finset.univ \ A).filter (fun y => y.val < c.val)).card = i.val := by
    rw [hc]; exact card_filter_val_lt_orderEmbOfFin _ hcard i
  have hset : (Finset.univ \ A).filter (fun y => y.val < c.val + 1)
      = ((Finset.univ \ A).filter (fun y => y.val < c.val)) ∪ {c} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, hlt⟩
      by_cases h : y = c
      · exact Or.inr h
      · left; refine ⟨hy, ?_⟩
        have hv : y.val ≠ c.val := fun hh => h (Fin.ext hh)
        omega
    · rintro (⟨hy, hlt⟩ | rfl)
      · exact ⟨hy, by omega⟩
      · exact ⟨hcmem, by omega⟩
  have hdisj : Disjoint ((Finset.univ \ A).filter (fun y => y.val < c.val))
      ({c} : Finset (Fin M)) := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_filter, not_and]
    intro _ h; omega
  have hcnt : cntB A (c.val + 1)
      = ((Finset.univ \ A).filter (fun y => y.val < c.val + 1)).card := rfl
  rw [hcnt, hset, Finset.card_union_of_disjoint hdisj, Finset.card_singleton, hrank]

end

end Work.Cohomology.EZG

namespace Work.Cohomology.EZG

noncomputable section

open CategoryTheory Simplicial Opposite

/-- `cntB A` at the top threshold is the number of complement elements. -/
lemma cntB_top (P Q : ℕ) (A : Finset (Fin ((P+1)+Q+1))) (hA : A.card = P+1) :
    cntB A ((P+1)+Q+1) = Q+1 := by
  rw [Work.Cohomology.cntB_eq_sub A (le_refl ((P+1)+Q+1)),
      Work.Cohomology.cnt_eq_card A (le_refl ((P+1)+Q+1)), hA]
  omega

/-- If `cntB A k.val = 0` and `k` comes from the `b`-side, then `k.val = 0`. -/
lemma val_eq_zero_of_cntB_eq_zero (P Q : ℕ) (A : Finset (Fin ((P+1)+Q+1)))
    (hA : A.card = P+1) (k : Fin ((P+1)+Q+2))
    (hprev_or : k.val = 0 ∨ k.val = (P+1)+Q+1 ∨
      (⟨k.val - 1, by omega⟩ : Fin ((P+1)+Q+1)) ∉ A)
    (hk : cntB A k.val = 0) : k.val = 0 := by
  by_contra hk0
  rcases hprev_or with h0 | hlast | hprev
  · exact hk0 h0
  · rw [hlast, cntB_top P Q A hA] at hk; omega
  · have hkpos : 1 ≤ k.val := by omega
    have hlt := Work.Cohomology.cntB_lt_of_notMem A hprev
    have hv : k.val - 1 + 1 = k.val := by omega
    rw [hv] at hlt
    omega

/-- If `cntB A k.val = Q+1` and `k` comes from the `b`-side, then `k.val = (P+1)+Q+1`. -/
lemma val_eq_last_of_cntB_eq_top (P Q : ℕ) (A : Finset (Fin ((P+1)+Q+1)))
    (hA : A.card = P+1) (k : Fin ((P+1)+Q+2)) (hdel : delIdx k ∉ A)
    (hprev_or : k.val = 0 ∨ k.val = (P+1)+Q+1 ∨
      (⟨k.val - 1, by omega⟩ : Fin ((P+1)+Q+1)) ∉ A)
    (hk : cntB A k.val = Q+1) : k.val = (P+1)+Q+1 := by
  by_contra hkne
  rcases hprev_or with h0 | hlast | hprev
  · rw [h0] at hk; simp [cntB] at hk
  · exact hkne hlast
  · have hkpos : 1 ≤ k.val := by
      rcases Nat.eq_zero_or_pos k.val with hz | hp
      · rw [hz] at hk; simp [cntB] at hk
      · exact hp
    have hkle : k.val ≤ (P+1)+Q := by have := k.isLt; omega
    have hmem : (⟨k.val, by omega⟩ : Fin ((P+1)+Q+1)) ∈ Finset.univ \ A := by
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hdk : delIdx k = (⟨k.val, by omega⟩ : Fin ((P+1)+Q+1)) := by
        rw [Work.Cohomology.delIdx_of_le k hkle]
      rw [← hdk]; exact hdel
    have hsub : (Finset.univ \ A).filter (fun i : Fin ((P+1)+Q+1) => i.val < k.val) ⊆
        (Finset.univ \ A).erase (⟨k.val, by omega⟩ : Fin ((P+1)+Q+1)) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_erase]
      refine ⟨?_, hi.1⟩
      intro hcontra
      have h2 : (⟨k.val, by omega⟩ : Fin ((P+1)+Q+1)).val < k.val := by
        rw [← hcontra]; exact hi.2
      simp only [Fin.val_mk] at h2
      omega
    have hcardle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hmem] at hcardle
    rw [card_univ_sdiff_fin, hA] at hcardle
    simp only [cntB] at hk
    omega

end

end Work.Cohomology.EZG

namespace Work.Cohomology.EZG

noncomputable section

open CategoryTheory Simplicial Opposite

/-- `orderEmbOfFin` does not depend on the particular proof of the cardinality. -/
lemma orderEmbOfFin_congr_card' {α : Type*} [LinearOrder α] {s : Finset α} {k : ℕ}
    {h₁ : s.card = k} (h₂ : s.card = k) {i : Fin k} :
    s.orderEmbOfFin h₁ i = s.orderEmbOfFin h₂ i :=
  Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr rfl

/-- `delIdx` of `Fin.succ (Fin.castSucc c)` is `Fin.succ c`. -/
lemma delIdx_succ_castSucc {N : ℕ} (c : Fin N) :
    delIdx (Fin.succ (Fin.castSucc c)) = Fin.succ c := by
  ext; rw [Work.Cohomology.delIdx_val]
  simp only [Fin.val_succ, Fin.val_castSucc]; omega

end

end Work.Cohomology.EZG

namespace Work.Cohomology.EZG

noncomputable section

open CategoryTheory Simplicial Opposite

theorem b_roundtrips (P Q : ℕ) :
    (∀ y : TargetB P Q, IsB ((P+1)+Q) (bInvIdx P Q y).1.1 (bInvIdx P Q y).2) ∧
    (∀ (y : TargetB P Q) (h : IsB ((P+1)+Q) (bInvIdx P Q y).1.1 (bInvIdx P Q y).2),
        bFwd P Q ⟨bInvIdx P Q y, h⟩ = y) ∧
    (∀ (x : Idx P Q) (h : IsB ((P+1)+Q) x.1.1 x.2),
        bInvIdx P Q (bFwd P Q ⟨x, h⟩) = x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨⟨A'', hA''⟩, j⟩ := y
    by_cases hj0 : j.val = 0
    · simp only [bInvIdx, dif_pos hj0]
      refine ⟨?_, Or.inl rfl⟩
      show delIdx (0 : Fin ((P+1)+Q+2)) ∉ shUp A'' (0 : Fin ((P+1)+Q+1))
      rw [show delIdx (0 : Fin ((P+1)+Q+2)) = (0 : Fin ((P+1)+Q+1)) from by
        ext; simp [Work.Cohomology.delIdx]]
      exact notMem_shUp A'' 0
    · by_cases hjQ : j.val = Q+1
      · simp only [bInvIdx, dif_neg hj0, dif_pos hjQ]
        refine ⟨?_, Or.inr (Or.inl rfl)⟩
        show delIdx (Fin.last ((P+1)+Q+1)) ∉ shUp A'' (Fin.last ((P+1)+Q))
        rw [show delIdx (Fin.last ((P+1)+Q+1)) = Fin.last ((P+1)+Q) from by
          ext; rw [Work.Cohomology.delIdx_val, Fin.val_last, Fin.val_last]; simp]
        exact notMem_shUp A'' _
      · simp only [bInvIdx, dif_neg hj0, dif_neg hjQ]
        set c := (Finset.univ \ A'').orderEmbOfFin
          (by rw [card_univ_sdiff_fin]; have := hA''; omega :
            (Finset.univ \ A'').card = Q)
          (⟨j.val - 1, by omega⟩ : Fin Q) with hc
        refine ⟨?_, Or.inr (Or.inr ?_)⟩
        · show delIdx (Fin.succ (Fin.castSucc c)) ∉ shUp A'' (Fin.succ c)
          rw [delIdx_succ_castSucc]
          exact notMem_shUp A'' (Fin.succ c)
        · show c.castSucc ∉ shUp A'' (Fin.succ c)
          have hcmem : c ∈ Finset.univ \ A'' := by
            rw [hc]; exact Finset.orderEmbOfFin_mem _ _ ⟨j.val - 1, by omega⟩
          have hcA'' : c ∉ A'' := (Finset.mem_sdiff.mp hcmem).2
          have hcs : Fin.succAbove (Fin.succ c) c = c.castSucc :=
            succAbove_eq_of_lt _ c (by simp)
          intro hmem
          rw [shUp, Finset.mem_image] at hmem
          obtain ⟨t, ht, heq⟩ := hmem
          rw [← hcs] at heq
          exact hcA'' (Fin.succAbove_right_injective heq ▸ ht)
  · intro y h
    obtain ⟨⟨A'', hA''⟩, j⟩ := y
    by_cases hj0 : j.val = 0
    · simp only [bFwd, bInvIdx, dif_pos hj0]
      refine Prod.ext ?_ ?_
      · refine Subtype.ext ?_
        show delPosP (shUp A'' (0 : Fin ((P+1)+Q+1))) (delIdx (0 : Fin ((P+1)+Q+2))) = A''
        rw [show delIdx (0 : Fin ((P+1)+Q+2)) = (0 : Fin ((P+1)+Q+1)) from by
          ext; simp [Work.Cohomology.delIdx]]
        exact delPosP_shUp A'' 0
      · refine Fin.ext ?_
        show cntB (shUp A'' (0 : Fin ((P+1)+Q+1))) (0 : Fin ((P+1)+Q+2)).val = j.val
        rw [hj0]; simp [cntB]
    · by_cases hjQ : j.val = Q+1
      · simp only [bFwd, bInvIdx, dif_neg hj0, dif_pos hjQ]
        refine Prod.ext ?_ ?_
        · refine Subtype.ext ?_
          show delPosP (shUp A'' (Fin.last ((P+1)+Q))) (delIdx (Fin.last ((P+1)+Q+1))) = A''
          rw [show delIdx (Fin.last ((P+1)+Q+1)) = Fin.last ((P+1)+Q) from by
            ext; rw [Work.Cohomology.delIdx_val, Fin.val_last, Fin.val_last]; simp]
          exact delPosP_shUp A'' _
        · refine Fin.ext ?_
          show cntB (shUp A'' (Fin.last ((P+1)+Q))) (Fin.last ((P+1)+Q+1)).val = j.val
          rw [Fin.val_last, hjQ, cntB_eq_sub _ (le_refl ((P+1)+Q+1)),
            cnt_eq_card _ (le_refl ((P+1)+Q+1)), shUp_card, hA'']
          omega
      · simp only [bFwd, bInvIdx, dif_neg hj0, dif_neg hjQ]
        set c := (Finset.univ \ A'').orderEmbOfFin
          (by rw [card_univ_sdiff_fin]; have := hA''; omega :
            (Finset.univ \ A'').card = Q)
          (⟨j.val - 1, by omega⟩ : Fin Q) with hc
        refine Prod.ext ?_ ?_
        · refine Subtype.ext ?_
          show delPosP (shUp A'' (Fin.succ c)) (delIdx (Fin.succ (Fin.castSucc c))) = A''
          rw [delIdx_succ_castSucc]
          exact delPosP_shUp A'' (Fin.succ c)
        · refine Fin.ext ?_
          show cntB (shUp A'' (Fin.succ c)) (Fin.succ (Fin.castSucc c)).val = j.val
          rw [show (Fin.succ (Fin.castSucc c)).val = c.val + 1 from by
            simp only [Fin.val_succ, Fin.val_castSucc]]
          rw [cntB_shUp_of_le A'' (Fin.succ c)
            (le_of_eq (by simp only [Fin.val_succ]))]
          have hMY : (Finset.univ \ A'').card = Q := by
            rw [card_univ_sdiff_fin, hA'']
            exact Nat.add_sub_cancel_left _ _
          have hoc : cntB A'' (c.val + 1) = j.val := by
            rw [hc]
            rw [orderEmbOfFin_congr_card' hMY]
            rw [cntB_orderEmb_compl A'' hMY (⟨j.val - 1, by omega⟩ : Fin Q)]
            simp only [Fin.val_mk]
            omega
          exact hoc
  · intro x h
    obtain ⟨⟨A, hA⟩, k⟩ := x
    have hp : delIdx k ∉ A := h.1
    have hA'' : (delPosP A (delIdx k)).card = P+1 := by
      rw [delPosP_card_of_notMem h.1]; exact hA
    have hcalc : bFwd P Q ⟨(⟨A,hA⟩,k), h⟩ =
        (⟨delPosP A (delIdx k), hA''⟩, (⟨cntB A k.val,
          by have := cntB_le_card A k.val; have := hA; omega⟩ : Fin (Q+2))) := by
      simp only [bFwd]
    rw [hcalc]
    by_cases hj0 : cntB A k.val = 0
    · have hk0 : k.val = 0 := val_eq_zero_of_cntB_eq_zero P Q A hA k h.2 hj0
      have hdel : delIdx k = (0 : Fin ((P+1)+Q+1)) := by
        rw [Work.Cohomology.delIdx_of_le k (by omega)]
        ext; simp [hk0]
      simp only [bInvIdx, dif_pos hj0]
      refine Prod.ext ?_ ?_
      · refine Subtype.ext ?_
        show shUp (delPosP A (delIdx k)) (0 : Fin ((P+1)+Q+1)) = A
        rw [hdel]
        exact shUp_delPosP_of_notMem A 0 (by rw [← hdel]; exact hp)
      · refine Fin.ext ?_
        show (0 : Fin ((P+1)+Q+2)).val = k.val
        rw [hk0]; simp
    · by_cases hjQ : cntB A k.val = Q+1
      · have hklast : k.val = (P+1)+Q+1 := val_eq_last_of_cntB_eq_top P Q A hA k h.1 h.2 hjQ
        have hdel : delIdx k = Fin.last ((P+1)+Q) :=
          Work.Cohomology.delIdx_of_val k hklast
        simp only [bInvIdx, dif_neg hj0, dif_pos hjQ]
        refine Prod.ext ?_ ?_
        · refine Subtype.ext ?_
          show shUp (delPosP A (delIdx k)) (Fin.last ((P+1)+Q)) = A
          rw [hdel]
          exact shUp_delPosP_of_notMem A (Fin.last ((P+1)+Q)) (by rw [← hdel]; exact hp)
        · refine Fin.ext ?_
          show (Fin.last ((P+1)+Q+1)).val = k.val
          rw [hklast]; simp [Fin.val_last]
      · have hk0 : k.val ≠ 0 := by intro h0; exact hj0 (by rw [h0]; simp [cntB])
        have hklast : k.val ≠ (P+1)+Q+1 := by
          intro hl; exact hjQ (by rw [hl, cntB_top P Q A hA])
        have hprev : (⟨k.val - 1, by omega⟩ : Fin ((P+1)+Q+1)) ∉ A := by
          rcases h.2 with h0 | hlast | hprev
          · exact absurd h0 hk0
          · exact absurd hlast hklast
          · exact hprev
        have hkpos : 1 ≤ k.val := by omega
        have hcB : cntB A k.val ≤ Q := by
          have h1 := cntB_le_card A k.val
          rw [hA] at h1
          rw [show (P+1)+(Q+1)-(P+1) = Q+1 from Nat.add_sub_cancel_left _ _] at h1
          omega
        have hkle : k.val ≤ (P+1)+Q := by have := k.isLt; omega
        have hdelk : delIdx k = (⟨k.val, by omega⟩ : Fin ((P+1)+Q+1)) :=
          Work.Cohomology.delIdx_of_le k hkle
        have hdv : (delIdx k).val = k.val := by rw [hdelk]
        have hMY : (Finset.univ \ delPosP A (delIdx k)).card = Q := by
          rw [card_univ_sdiff_fin]
          have hcd : (delPosP A (delIdx k)).card = P+1 := by
            rw [delPosP_card_of_notMem h.1]; exact hA
          rw [hcd]; exact Nat.add_sub_cancel_left _ _
        have hval : (Finset.univ \ delPosP A (delIdx k)).orderEmbOfFin hMY
            (⟨cntB A k.val - 1, by omega⟩ : Fin Q) = (⟨k.val - 1, by omega⟩ : Fin ((P+1)+Q)) := by
          refine orderEmbOfFin_eq_of_card_filter_val_lt _ hMY ?_ ?_
          · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
            rw [hdelk, mem_delPosP]
            have hsa : Fin.succAbove (⟨k.val, by omega⟩ : Fin ((P+1)+Q+1))
                (⟨k.val - 1, by omega⟩ : Fin ((P+1)+Q))
                = (⟨k.val - 1, by omega⟩ : Fin ((P+1)+Q+1)) := by
              rw [succAbove_eq_of_lt _ _ (by simp only [Fin.val_mk]; omega)]
              exact Fin.ext (by simp only [Fin.val_castSucc, Fin.val_mk])
            rw [hsa]
            exact hprev
          · have hcomp := card_filter_lt_comp_delPosP A (delIdx k) h.1
                (by rw [hdv]; exact hkpos)
                (by
                  have hfin : (⟨(delIdx k).val - 1, by omega⟩ : Fin ((P+1)+Q+1)) =
                      (⟨k.val - 1, by omega⟩ : Fin ((P+1)+Q+1)) := by
                    apply Fin.ext
                    show (delIdx k).val - 1 = k.val - 1
                    rw [hdv]
                  rw [hfin]; exact hprev)
            rw [hdelk] at hcomp
            simpa [hdelk] using hcomp
        simp only [bInvIdx, dif_neg hj0, dif_neg hjQ]
        refine Prod.ext ?_ ?_
        · refine Subtype.ext ?_
          show shUp (delPosP A (delIdx k))
            (Fin.succ ((Finset.univ \ delPosP A (delIdx k)).orderEmbOfFin _ _)) = A
          rw [orderEmbOfFin_congr_card' hMY]
          rw [hval]
          rw [show (Fin.succ (⟨k.val - 1, by omega⟩ : Fin ((P+1)+Q))) = delIdx k from by
            rw [hdelk]; exact Fin.ext (by simp only [Fin.val_succ, Fin.val_mk]; omega)]
          exact shUp_delPosP_of_notMem A (delIdx k) h.1
        · refine Fin.ext ?_
          show (Fin.succ (Fin.castSucc
            ((Finset.univ \ delPosP A (delIdx k)).orderEmbOfFin _ _))).val = k.val
          rw [orderEmbOfFin_congr_card' hMY]
          rw [hval]
          simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_mk]
          omega

end

end Work.Cohomology.EZG
