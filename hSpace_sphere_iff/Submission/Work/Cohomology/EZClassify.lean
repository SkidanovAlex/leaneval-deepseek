/-
# The faces of a staircase simplex

For a shuffle `A ⊆ Fin (N+1)` of `(P+1, Q+1)`-type (i.e. `|A| = P+1`), the `k`-th face of
the staircase map `shA A` is either

* the `a`-side face: it equals `shA (delPos A k)` followed by the `i`-th face of the `(P+1)`-simplex
  with `i = cnt A k`, when the letter at the deleted position of `A` is an `a`-letter and, for an
  interior face, so is the previous letter, and
* the `b`-side face: it equals `shB (delPos A k)` followed by the `j`-th face, when the deleted
  letter is a `b`-letter and (interior case) so is the previous one.
-/
import Mathlib
import Submission.Work.Cohomology.EZShuffleGen
import Submission.Work.Cohomology.EZG.cnt_succAbove
import Submission.Work.Cohomology.EZG.cnt_cross
import Submission.Work.Cohomology.EZG.cntB_cross

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

noncomputable section

variable {X Y : SSet.{0}}

lemma cntB_eq_sub {n : ℕ} (A : Finset (Fin n)) {m : ℕ} (hm : m ≤ n) :
    cntB A m = m - cnt A m := by
  have := cnt_add_cntB A hm
  omega

/-- `cnt` is bounded by the threshold (for thresholds below the ambient degree). -/
lemma cnt_le_self {n : ℕ} (A : Finset (Fin n)) {m : ℕ} (hm : m ≤ n) : cnt A m ≤ m := by
  rw [cnt]
  refine le_trans (Finset.card_le_card ?_) (le_of_eq (card_filter_lt hm))
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.2

/-- The value of `Fin.succAbove`, in the "shift by the indicator" form. -/
lemma val_succAbove' {m : ℕ} (p : Fin (m+1)) (i : Fin m) :
    (Fin.succAbove p i).val = i.val + (if (p:ℕ) ≤ (i:ℕ) then 1 else 0) := by
  rw [EZG.val_succAbove_aux]
  by_cases h : (i:ℕ) < (p:ℕ)
  · rw [if_pos h, if_neg (by omega), add_zero]
  · rw [if_neg h, if_pos (by omega)]

lemma shA_apply {n p : ℕ} (A : Finset (Fin n)) (h : A.card ≤ p) (j : Fin (n+1)) :
    (shA A h).toOrderHom j =
      ⟨cnt A j.val, Nat.lt_succ_of_le (le_trans (cnt_le_card A _) h)⟩ := rfl

lemma shB_apply {n q : ℕ} (A : Finset (Fin n)) (h : n ≤ A.card + q) (j : Fin (n+1)) :
    (shB A h).toOrderHom j =
      ⟨cntB A j.val, by
        have h2 : n - A.card ≤ q := by omega
        exact Nat.lt_succ_of_le (le_trans (cntB_le_card A j.val) h2)⟩ := rfl

lemma delta_toOrderHom {n : ℕ} (k : Fin (n+2)) :
    (SimplexCategory.δ k).toOrderHom = Fin.succAbove k := rfl

/-- Deleting a position that does not belong to the shuffle preserves the cardinality. -/
lemma delPosP_card_of_notMem {n : ℕ} {A : Finset (Fin (n+1))} {p : Fin (n+1)} (hp : p ∉ A) :
    (delPosP A p).card = A.card := by
  have hinj : Function.Injective (fun t : Fin n => Fin.succAbove p t) := Fin.succAbove_right_injective
  have hmap : (delPosP A p).map ⟨_, hinj⟩ = A := by
    ext q
    rw [Finset.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact mem_delPosP.mp ht
    · intro hq
      have hqp : q ≠ p := fun h => hp (h ▸ hq)
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hqp
      exact ⟨t, mem_delPosP.mpr (by rw [ht]; exact hq), ht⟩
  rw [← Finset.card_map (f := ⟨_, hinj⟩), hmap]

/-- The prefix correspondence, at the level of the vertices of the target simplex. -/
lemma cnt_succAbove_top {n : ℕ} (A : Finset (Fin (n+1))) (p : Fin (n+1)) (j : Fin (n+1)) :
    cnt A (Fin.succAbove (Fin.castSucc p) j).val
      = cnt (delPosP A p) j.val + (if p ∈ A ∧ (p:ℕ) ≤ (j:ℕ) then 1 else 0) := by
  rcases Nat.lt_or_ge (j:ℕ) n with hj | hj
  · have h := EZG.cnt_succAbove A p (⟨j.val, hj⟩ : Fin n)
    rw [val_succAbove'] at h
    rw [val_succAbove']
    simpa using h
  · have hjn : (j:ℕ) = n := by omega
    have h1 : cnt A (Fin.succAbove (Fin.castSucc p) j).val = A.card := by
      have hv : (Fin.succAbove (Fin.castSucc p) j).val = n + 1 := by
        have hple : (Fin.castSucc p : Fin (n+2)).val ≤ (j:ℕ) := by
          simp only [Fin.val_castSucc]; omega
        rw [val_succAbove', if_pos hple, hjn]
      rw [hv, cnt_eq_card A (le_refl (n+1))]
    have h2 : cnt (delPosP A p) j.val = (delPosP A p).card := by
      rw [hjn, cnt_eq_card (delPosP A p) (le_refl n)]
    rw [h1, h2]
    by_cases hp : p ∈ A
    · rw [delPosP_card hp, if_pos ⟨hp, by omega⟩]
      have hpos : 0 < A.card := Finset.card_pos.mpr ⟨p, hp⟩
      omega
    · rw [delPosP_card_of_notMem hp, if_neg (fun h => hp h.1), add_zero]

lemma cnt_succ_of_mem_fin {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (hA : t ∈ A) :
    cnt A (t.val + 1) = cnt A t.val + 1 := by
  have hf : A.filter (fun i : Fin n => i.val < t.val + 1) =
      A.filter (fun i : Fin n => i.val < t.val) ∪ {t} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hiA, hi⟩
      by_cases h : i = t
      · exact Or.inr h
      · have hne : (i:ℕ) ≠ t.val := fun hh => h (Fin.ext hh)
        exact Or.inl ⟨hiA, by omega⟩
    · rintro (⟨hiA, hi⟩ | rfl)
      · exact ⟨hiA, by omega⟩
      · exact ⟨hA, by simp⟩
  have hdisj : Disjoint (A.filter (fun i : Fin n => i.val < t.val)) {t} := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_filter, not_and]
    intro _
    omega
  rw [cnt, cnt, hf, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]

/-- Strict monotonicity of `cntB` at an element outside `A`. -/
lemma cntB_lt_of_notMem {n : ℕ} (A : Finset (Fin n)) {t : Fin n} (ht : t ∉ A) :
    cntB A t.val < cntB A (t.val + 1) := by
  have hsub : (Finset.univ \ A).filter (fun i : Fin n => i.val < t.val) ⊂
      (Finset.univ \ A).filter (fun i : Fin n => i.val < t.val + 1) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun i hi => ?_, ?_⟩
    · simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, by omega⟩
    · intro hcon
      have : t ∈ (Finset.univ \ A).filter (fun i : Fin n => i.val < t.val) := by
        rw [hcon]; exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ht⟩, by omega⟩
      simp only [Finset.mem_filter] at this
      omega
  exact Finset.card_lt_card hsub

/-- The crossing statement, extended to the last vertex. -/
lemma cnt_cross_top {n : ℕ} (A : Finset (Fin (n+1))) (q : Fin n)
    (hq : q.castSucc ∈ A) (hq' : q.succ ∈ A) (j : Fin (n+1)) :
    cnt A q.succ.val ≤ cnt (delPosP A q.succ) j.val ↔ (q:ℕ) < (j:ℕ) := by
  rcases Nat.lt_or_ge (j:ℕ) n with hj | hj
  · exact EZG.cnt_cross A q hq hq' (⟨j.val, hj⟩ : Fin n)
  · have hjn : (j:ℕ) = n := by omega
    constructor
    · intro _; omega
    · intro _
      have hc : cnt (delPosP A q.succ) j.val = (delPosP A q.succ).card := by
        rw [hjn, cnt_eq_card (delPosP A q.succ) (le_refl n)]
      rw [hc, delPosP_card hq']
      have h1 : cnt A q.succ.val + 1 ≤ A.card := by
        rw [← cnt_succ_of_mem_fin A q.succ hq']
        exact cnt_le_card A (q.succ.val + 1)
      omega

/-- The `b`-side crossing statement, extended to the last vertex. -/
lemma cntB_cross_top {n : ℕ} (A : Finset (Fin (n+1))) (q : Fin n)
    (hq : q.castSucc ∉ A) (hq' : q.succ ∉ A) (j : Fin (n+1)) :
    cntB A q.succ.val ≤ cntB (delPosP A q.succ) j.val ↔ (q:ℕ) < (j:ℕ) := by
  rcases Nat.lt_or_ge (j:ℕ) n with hj | hj
  · exact EZG.cntB_cross A q hq hq' (⟨j.val, hj⟩ : Fin n)
  · have hjn : (j:ℕ) = n := by omega
    constructor
    · intro _; omega
    · intro _
      have hcard : (delPosP A q.succ).card = A.card := delPosP_card_of_notMem hq'
      have h2 : cnt (delPosP A q.succ) n = A.card := by
        rw [cnt_eq_card (delPosP A q.succ) (le_refl n), hcard]
      rw [hjn, cntB_eq_sub (delPosP A q.succ) (le_refl n), h2]
      have hstrict : cntB A q.succ.val < cntB A (q.succ.val + 1) := cntB_lt_of_notMem A hq'
      have hmono : cntB A (q.succ.val + 1) ≤ cntB A (n+1) := cntB_mono A (by omega)
      have hfull : cntB A (n+1) = n + 1 - A.card := by
        rw [cntB_eq_sub A (le_refl (n+1)), cnt_eq_card A (le_refl (n+1))]
      have hAcard : A.card ≤ n + 1 := by
        simpa using Finset.card_le_card (Finset.subset_univ A)
      omega

/-! ### The classification of the faces

The four interior cases, for the face with index `q+1` (`q : Fin N`): if the letters of the word of
`A` at positions `q` and `q+1` are both `a`-letters (resp. both `b`-letters), the face is an
`a`-side (resp. `b`-side) face. -/

/-- Interior `a`-face of the `a`-shuffle map. -/
theorem faceA_mid {N P : ℕ} (A : Finset (Fin (N+1))) (hA : A.card ≤ P+1) (q : Fin N)
    (hq : q.castSucc ∈ A) (hq' : q.succ ∈ A) :
    (SimplexCategory.δ (Fin.castSucc q.succ) ≫ shA A hA) =
      (shA (delPosP A q.succ) (by rw [delPosP_card hq']; omega) ≫
        SimplexCategory.δ (⟨cnt A q.succ.val,
          by have := cnt_le_card A q.succ.val; omega⟩ : Fin (P+2))) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    shA_apply, delta_toOrderHom, val_succAbove', Fin.val_castSucc]
  have hjN : (j:ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  rcases Nat.lt_or_ge (j:ℕ) N with hj | hj
  · have h := EZG.cnt_succAbove A q.succ (⟨j.val, hj⟩ : Fin N)
    simp only [val_succAbove'] at h
    rw [h]
    by_cases hc : (q:ℕ) < (j:ℕ)
    · have hs : (q.succ:ℕ) ≤ (j:ℕ) := by simp only [Fin.val_succ]; omega
      have hk : cnt A q.succ.val ≤ cnt (delPosP A q.succ) j.val :=
        (cnt_cross_top A q hq hq' j).mpr hc
      rw [if_pos (show q.succ ∈ A ∧ (q.succ:ℕ) ≤ (j:ℕ) from ⟨hq', hs⟩), if_pos hk]
    · have hs : ¬ ((q.succ:ℕ) ≤ (j:ℕ)) := by simp only [Fin.val_succ]; omega
      have hk : ¬ (cnt A q.succ.val ≤ cnt (delPosP A q.succ) j.val) :=
        fun hh => hc ((cnt_cross_top A q hq hq' j).mp hh)
      rw [if_neg (show ¬ (q.succ ∈ A ∧ (q.succ:ℕ) ≤ (j:ℕ)) from fun h => hs h.2), if_neg hk]
  · have hjn : (j:ℕ) = N := by omega
    have hs : (q.succ:ℕ) ≤ (j:ℕ) := by simp only [Fin.val_succ]; omega
    have hstrict : cnt A q.succ.val + 1 ≤ A.card := by
      rw [← cnt_succ_of_mem_fin A q.succ hq']
      exact cnt_le_card A (q.succ.val + 1)
    have h1 : cnt A ((j:ℕ) + (if (q.succ:ℕ) ≤ (j:ℕ) then 1 else 0)) = A.card := by
      rw [if_pos hs, hjn, cnt_eq_card A (le_refl (N+1))]
    have h3 : cnt A q.succ.val ≤ cnt (delPosP A q.succ) (j:ℕ) := by
      have h2 : cnt (delPosP A q.succ) (j:ℕ) = A.card - 1 := by
        rw [hjn, cnt_eq_card (delPosP A q.succ) (le_refl N), delPosP_card hq']
      rw [h2]; omega
    rw [h1, if_pos h3]
    have h2 : cnt (delPosP A q.succ) (j:ℕ) = A.card - 1 := by
      rw [hjn, cnt_eq_card (delPosP A q.succ) (le_refl N), delPosP_card hq']
    rw [h2]
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨q.succ, hq'⟩
    omega

/-- Interior `a`-face of the `b`-shuffle map. -/
theorem faceA_mid_g {N P Q : ℕ} (A : Finset (Fin (N+1))) (hA : A.card ≤ P+1)
    (hB : N + 1 ≤ A.card + (Q+1)) (q : Fin N)
    (hq : q.castSucc ∈ A) (hq' : q.succ ∈ A) :
    (SimplexCategory.δ (Fin.castSucc q.succ) ≫ shB A hB) =
      (shB (delPosP A q.succ) (by rw [delPosP_card hq']; omega)) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    shB_apply, delta_toOrderHom, val_succAbove', Fin.val_castSucc]
  have hjN : (j:ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  rcases Nat.lt_or_ge (j:ℕ) N with hj | hj
  · have h := EZG.cnt_succAbove A q.succ (⟨j.val, hj⟩ : Fin N)
    simp only [val_succAbove'] at h
    by_cases hc : (q:ℕ) < (j:ℕ)
    · have hs : (q.succ:ℕ) ≤ (j:ℕ) := by simp only [Fin.val_succ]; omega
      rw [if_pos (show (q.succ:ℕ) ≤ (j:ℕ) from hs),
        if_pos (show q.succ ∈ A ∧ (q.succ:ℕ) ≤ (j:ℕ) from ⟨hq', hs⟩)] at h
      rw [if_pos (show (q.succ:ℕ) ≤ (j:ℕ) from hs)]
      rw [cntB_eq_sub (A := A) (m := (j:ℕ) + 1) (by omega),
        cntB_eq_sub (A := delPosP A q.succ) (m := (j:ℕ)) (by omega), h]
      omega
    · have hs : ¬ ((q.succ:ℕ) ≤ (j:ℕ)) := by simp only [Fin.val_succ]; omega
      rw [if_neg (show ¬ ((q.succ:ℕ) ≤ (j:ℕ)) from hs),
        if_neg (show ¬ (q.succ ∈ A ∧ (q.succ:ℕ) ≤ (j:ℕ)) from fun h => hs h.2)] at h
      simp only [add_zero] at h
      rw [if_neg (show ¬ ((q.succ:ℕ) ≤ (j:ℕ)) from hs), add_zero]
      rw [cntB_eq_sub (A := A) (m := (j:ℕ)) (by omega),
        cntB_eq_sub (A := delPosP A q.succ) (m := (j:ℕ)) (by omega), h]
      try omega
  · have hjn : (j:ℕ) = N := by omega
    have hs : (q.succ:ℕ) ≤ (j:ℕ) := by simp only [Fin.val_succ]; omega
    rw [if_pos (show (q.succ:ℕ) ≤ (j:ℕ) from hs)]
    have h1 : cnt A ((j:ℕ) + 1) = A.card := by
      rw [hjn, cnt_eq_card A (le_refl (N+1))]
    have h2 : cnt (delPosP A q.succ) (j:ℕ) = A.card - 1 := by
      rw [hjn, cnt_eq_card (delPosP A q.succ) (le_refl N), delPosP_card hq']
    rw [cntB_eq_sub (A := A) (m := (j:ℕ) + 1) (by omega),
      cntB_eq_sub (A := delPosP A q.succ) (m := (j:ℕ)) (by omega), h1, h2]
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨q.succ, hq'⟩
    omega

/-- Interior `b`-face of the `a`-shuffle map. -/
theorem faceB_mid {N P : ℕ} (A : Finset (Fin (N+1))) (hA : A.card ≤ P+1) (q : Fin N)
    (hq : q.castSucc ∉ A) (hq' : q.succ ∉ A) :
    (SimplexCategory.δ (Fin.castSucc q.succ) ≫ shA A hA) =
      (shA (delPosP A q.succ) (by rw [delPosP_card_of_notMem hq']; exact hA)) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    shA_apply, delta_toOrderHom, val_succAbove', Fin.val_castSucc]
  have hjN : (j:ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  rcases Nat.lt_or_ge (j:ℕ) N with hj | hj
  · have h := EZG.cnt_succAbove A q.succ (⟨j.val, hj⟩ : Fin N)
    simp only [val_succAbove'] at h
    rw [h, if_neg (show ¬ (q.succ ∈ A ∧ (q.succ:ℕ) ≤ (j:ℕ)) from fun hh => hq' hh.1), add_zero]
  · have hjn : (j:ℕ) = N := by omega
    have hs : (q.succ:ℕ) ≤ (j:ℕ) := by simp only [Fin.val_succ]; omega
    have h1 : cnt A ((j:ℕ) + (if (q.succ:ℕ) ≤ (j:ℕ) then 1 else 0)) = A.card := by
      rw [if_pos hs, hjn, cnt_eq_card A (le_refl (N+1))]
    have h2 : cnt (delPosP A q.succ) (j:ℕ) = A.card := by
      rw [hjn, cnt_eq_card (delPosP A q.succ) (le_refl N), delPosP_card_of_notMem hq']
    rw [h1, h2]

/-- Interior `b`-face of the `b`-shuffle map. -/
theorem faceB_mid_g {N P Q : ℕ} (A : Finset (Fin (N+1))) (hA : A.card ≤ P+1)
    (hB : N + 1 ≤ A.card + (Q+1)) (q : Fin N)
    (hq : q.castSucc ∉ A) (hq' : q.succ ∉ A) :
    (SimplexCategory.δ (Fin.castSucc q.succ) ≫ shB A hB) =
      (shB (delPosP A q.succ) (by rw [delPosP_card_of_notMem hq']; omega) ≫
        SimplexCategory.δ (⟨cntB A q.succ.val,
          by have := cntB_le_card A q.succ.val; omega⟩ : Fin (Q+2))) := by
  ext j
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    shB_apply, delta_toOrderHom, val_succAbove', Fin.val_castSucc]
  have hjN : (j:ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  rcases Nat.lt_or_ge (j:ℕ) N with hj | hj
  · have h := EZG.cnt_succAbove A q.succ (⟨j.val, hj⟩ : Fin N)
    simp only [val_succAbove'] at h
    rw [if_neg (show ¬ (q.succ ∈ A ∧ (q.succ:ℕ) ≤ (j:ℕ)) from fun hh => hq' hh.1)] at h
    by_cases hc : (q:ℕ) < (j:ℕ)
    · have hs : (q.succ:ℕ) ≤ (j:ℕ) := by simp only [Fin.val_succ]; omega
      have hk : cntB A q.succ.val ≤ cntB (delPosP A q.succ) j.val :=
        (cntB_cross_top A q hq hq' j).mpr hc
      rw [if_pos (show (q.succ:ℕ) ≤ (j:ℕ) from hs)] at h
      rw [if_pos (show (q.succ:ℕ) ≤ (j:ℕ) from hs), if_pos hk]
      have hb1 : cntB A ((j:ℕ) + 1) = ((j:ℕ) + 1) - cnt A ((j:ℕ) + 1) :=
        cntB_eq_sub (A := A) (m := (j:ℕ) + 1) (by omega)
      have hb2 : cntB (delPosP A q.succ) (j:ℕ) = (j:ℕ) - cnt (delPosP A q.succ) (j:ℕ) :=
        cntB_eq_sub (A := delPosP A q.succ) (m := (j:ℕ)) (by omega)
      have hle : cnt (delPosP A q.succ) (j:ℕ) ≤ (j:ℕ) := cnt_le_self _ (by omega)
      rw [hb1, hb2, h]
      omega
    · have hs : ¬ ((q.succ:ℕ) ≤ (j:ℕ)) := by simp only [Fin.val_succ]; omega
      have hk : ¬ (cntB A q.succ.val ≤ cntB (delPosP A q.succ) j.val) :=
        fun hh => hc ((cntB_cross_top A q hq hq' j).mp hh)
      rw [if_neg (show ¬ ((q.succ:ℕ) ≤ (j:ℕ)) from hs)] at h
      rw [if_neg (show ¬ ((q.succ:ℕ) ≤ (j:ℕ)) from hs), if_neg hk]
      have hb1 : cntB A ((j:ℕ) + 0) = (j:ℕ) - cnt A ((j:ℕ) + 0) :=
        cntB_eq_sub (A := A) (m := (j:ℕ)) (by omega)
      have hb2 : cntB (delPosP A q.succ) (j:ℕ) = (j:ℕ) - cnt (delPosP A q.succ) (j:ℕ) :=
        cntB_eq_sub (A := delPosP A q.succ) (m := (j:ℕ)) (by omega)
      rw [hb1, hb2, h, add_zero]
      omega
  · have hjn : (j:ℕ) = N := by omega
    have hs : (q.succ:ℕ) ≤ (j:ℕ) := by simp only [Fin.val_succ]; omega
    have hk : cntB A q.succ.val ≤ cntB (delPosP A q.succ) (j:ℕ) :=
      (cntB_cross_top A q hq hq' j).mpr (by omega)
    rw [if_pos (show (q.succ:ℕ) ≤ (j:ℕ) from hs), if_pos hk]
    have h1 : cnt A ((j:ℕ) + 1) = A.card := by
      rw [hjn, cnt_eq_card A (le_refl (N+1))]
    have h2 : cnt (delPosP A q.succ) (j:ℕ) = A.card := by
      rw [hjn, cnt_eq_card (delPosP A q.succ) (le_refl N), delPosP_card_of_notMem hq']
    rw [cntB_eq_sub (A := A) (m := (j:ℕ) + 1) (by omega),
      cntB_eq_sub (A := delPosP A q.succ) (m := (j:ℕ)) (by omega), h1, h2]
    have hAcard : A.card ≤ N := by
      have h1 : A.card < (Finset.univ : Finset (Fin (N+1))).card := by
        refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ A, ?_⟩)
        intro hcon
        exact hq' (hcon ▸ Finset.mem_univ q.succ)
      simpa using h1
    omega

/-
TODO (next session): the four end cases for the `b`-shuffle map, following the pattern of
`faceA_mid_g` / `faceB_mid_g` (rewrite with `cntB_eq_sub` and `cnt_succAbove_top`, then `omega`):

theorem faceA_zero_g {N Q : ℕ} (A : Finset (Fin (N+1))) (hB : N + 1 ≤ A.card + (Q+1))
    (h0 : (0 : Fin (N+1)) ∈ A) :
    (δ 0 ≫ shB A hB) = (shB (delPosP A 0) (by rw [delPosP_card h0]; omega))

theorem faceA_last_g {N Q : ℕ} (A : Finset (Fin (N+1))) (hB : N + 1 ≤ A.card + (Q+1))
    (hN : (Fin.last N) ∈ A) :
    (δ (Fin.last (N+1)) ≫ shB A hB) =
      (shB (delPosP A (Fin.last N)) (by rw [delPosP_card hN]; omega))

theorem faceB_zero_g {N Q : ℕ} (A : Finset (Fin (N+1))) (hB : N + 1 ≤ A.card + (Q+1))
    (h0 : (0 : Fin (N+1)) ∉ A) :
    (δ 0 ≫ shB A hB) =
      (shB (delPosP A 0) (by rw [delPosP_card_of_notMem h0]; omega) ≫ δ 0)

theorem faceB_last_g {N Q : ℕ} (A : Finset (Fin (N+1))) (hB : N + 1 ≤ A.card + (Q+1))
    (hcard : A.card = Q + 1) (hN : (Fin.last N) ∉ A) :
    (δ (Fin.last (N+1)) ≫ shB A hB) =
      (shB (delPosP A (Fin.last N)) (by rw [delPosP_card_of_notMem hN]; omega) ≫
        δ (Fin.last (Q+1)))
-/

end

end Work.Cohomology
