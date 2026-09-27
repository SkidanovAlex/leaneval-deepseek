/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Infrastructure for the Eilenberg–Zilber shuffle lemma

The shuffle chain `ezChainB a b` of a `p`-simplex `a` and a `q`-simplex `b` is a sum over the
`(p,q)`-shuffles `A ⊆ Fin (p+q)`, with the associated "staircase" simplex.  To compute its
boundary one has to compare faces of staircases of an ambient degree `n` with staircases of a
*smaller* ambient degree — and the arithmetical expressions for the two ambient degrees
(`(p+1)+q` versus `p+(q+1)`) are only propositionally, not definitionally, equal.  We therefore
record here a degree-polymorphic version of the shuffle machinery, in which the ambient degree is
an explicit variable `n` and the target degrees `p`, `q` are also explicit.
-/
import Mathlib

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

noncomputable section

variable {X Y : SSet.{0}}

/-! ### Counting the elements below a threshold -/

/-- `cnt A m` is the number of elements of `A : Finset (Fin n)` that are `< m`. -/
def cnt {n : ℕ} (A : Finset (Fin n)) (m : ℕ) : ℕ := (A.filter fun i => i.val < m).card

/-- `cntB A m` is the number of elements of the complement of `A : Finset (Fin n)` that are
`< m`. -/
def cntB {n : ℕ} (A : Finset (Fin n)) (m : ℕ) : ℕ :=
  ((Finset.univ \ A).filter fun i => i.val < m).card

lemma cnt_mono {n : ℕ} (A : Finset (Fin n)) : Monotone (cnt A) := by
  intro m m' h
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, lt_of_lt_of_le hi.2 h⟩

lemma cntB_mono {n : ℕ} (A : Finset (Fin n)) : Monotone (cntB A) := by
  intro m m' h
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, lt_of_lt_of_le hi.2 h⟩

lemma cnt_le_card {n : ℕ} (A : Finset (Fin n)) (m : ℕ) : cnt A m ≤ A.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma cntB_le_card {n : ℕ} (A : Finset (Fin n)) (m : ℕ) : cntB A m ≤ n - A.card := by
  rw [cntB]
  refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, Fintype.card_fin]

/-- The number of elements of `Fin n` that are `< m`, for `m ≤ n`. -/
lemma card_filter_lt {n m : ℕ} (hm : m ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m)).card = m := by
  rw [← Fintype.card_subtype (fun i : Fin n => i.val < m)]
  have e : {i : Fin n // i.val < m} ≃ Fin m :=
    { toFun := fun x => ⟨x.1.val, x.2⟩
      invFun := fun y => ⟨⟨y.1, lt_of_lt_of_le y.2 hm⟩, y.2⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  rw [Fintype.card_congr e]
  exact Fintype.card_fin m

lemma cnt_add_cntB {n : ℕ} (A : Finset (Fin n)) {m : ℕ} (hm : m ≤ n) :
    cnt A m + cntB A m = m := by
  have hd : Disjoint (A.filter fun i : Fin n => i.val < m)
      ((Finset.univ \ A).filter fun i : Fin n => i.val < m) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hi hi'
    exact hi'.1 hi.1
  have hun : (A.filter fun i : Fin n => i.val < m) ∪
      ((Finset.univ \ A).filter fun i : Fin n => i.val < m) =
      Finset.univ.filter (fun i : Fin n => i.val < m) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      true_and]
    constructor
    · rintro (h | h) <;> exact h.2
    · intro h
      by_cases hi : i ∈ A
      · exact Or.inl ⟨hi, h⟩
      · refine Or.inr ⟨?_, h⟩
        simp [hi]
  rw [cnt, cntB, ← Finset.card_union_of_disjoint hd, hun, card_filter_lt hm]

/-- `cnt A (m+1) = cnt A m + 1` when `m ∈ A`. -/
lemma cnt_succ_of_mem {n : ℕ} (A : Finset (Fin n)) {m : ℕ} (hm : m < n)
    (hA : (⟨m, hm⟩ : Fin n) ∈ A) : cnt A (m + 1) = cnt A m + 1 := by
  have hf : A.filter (fun i : Fin n => i.val < m + 1) =
      A.filter (fun i : Fin n => i.val < m) ∪ {(⟨m, hm⟩ : Fin n)} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hiA, hi⟩
      by_cases h : i = (⟨m, hm⟩ : Fin n)
      · exact Or.inr h
      · have hne : (i:ℕ) ≠ m := fun hh => h (Fin.ext hh)
        exact Or.inl ⟨hiA, by omega⟩
    · rintro (⟨hiA, hi⟩ | rfl)
      · exact ⟨hiA, by omega⟩
      · exact ⟨hA, by simp⟩
  have hdisj : Disjoint (A.filter (fun i : Fin n => i.val < m)) {(⟨m, hm⟩ : Fin n)} := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_filter, not_and]
    intro _
    omega
  rw [cnt, cnt, hf, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]

/-- Strict monotonicity of `cnt`: an element of `A` in `[m, m')` forces a strict increase. -/
lemma cnt_lt_cnt {n : ℕ} (A : Finset (Fin n)) {m m' : ℕ} (h : m < m')
    (t : Fin n) (ht : t ∈ A) (h1 : m ≤ t.val) (h2 : t.val < m') : cnt A m < cnt A m' := by
  have hsub : A.filter (fun i => i.val < m) ⊂ A.filter (fun i => i.val < m') := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun i hi => ?_, ?_⟩
    · simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, lt_trans hi.2 h⟩
    · intro hcon
      have : t ∈ A.filter (fun i => i.val < m) := by
        rw [hcon]; exact Finset.mem_filter.mpr ⟨ht, h2⟩
      simp only [Finset.mem_filter] at this
      omega
  exact Finset.card_lt_card hsub

/-- `cnt` reaches the cardinality of `A` beyond `n`. -/
lemma cnt_eq_card {n : ℕ} (A : Finset (Fin n)) {m : ℕ} (hm : n ≤ m) : cnt A m = A.card := by
  rw [cnt]
  congr 1
  exact Finset.filter_true_of_mem (fun i _ => lt_of_lt_of_le i.isLt hm)

/-! ### Deleting a position of a shuffle -/

/-- The position of the word removed by the `k`-th face map: `min k n`. -/
def delIdx {n : ℕ} (k : Fin (n+2)) : Fin (n+1) :=
  ⟨min k.val n, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma delIdx_val {n : ℕ} (k : Fin (n+2)) : (delIdx k).val = min k.val n := rfl

lemma delIdx_of_le {n : ℕ} (k : Fin (n+2)) (h : k.val ≤ n) :
    delIdx k = ⟨k.val, Nat.lt_succ_of_le h⟩ := by
  ext
  rw [delIdx_val, Nat.min_eq_left h]

lemma delIdx_of_val {n : ℕ} (k : Fin (n+2)) (h : k.val = n + 1) :
    delIdx k = ⟨n, Nat.lt_succ_self n⟩ := by
  ext
  rw [delIdx_val, h]
  exact min_eq_right (Nat.le_succ n)

/-- Deleting the position `p` of a shuffle `A ⊆ Fin (n+1)`: the set of positions whose image
under `Fin.succAbove p` lies in `A`. -/
def delPosP {n : ℕ} (A : Finset (Fin (n+1))) (p : Fin (n+1)) : Finset (Fin n) :=
  Finset.univ.filter (fun t : Fin n => Fin.succAbove p t ∈ A)

/-- Deleting the position removed by the `k`-th face. -/
def delPos {n : ℕ} (A : Finset (Fin (n+1))) (k : Fin (n+2)) : Finset (Fin n) :=
  delPosP A (delIdx k)

lemma mem_delPosP {n : ℕ} {A : Finset (Fin (n+1))} {p : Fin (n+1)} {t : Fin n} :
    t ∈ delPosP A p ↔ Fin.succAbove p t ∈ A := by
  simp [delPosP]

lemma mem_delPos {n : ℕ} {A : Finset (Fin (n+1))} {k : Fin (n+2)} {t : Fin n} :
    t ∈ delPos A k ↔ Fin.succAbove (delIdx k) t ∈ A := by
  simp [delPos, mem_delPosP]

/-- The number of elements of a shuffle after deleting a position. -/
lemma delPosP_card {n : ℕ} {A : Finset (Fin (n+1))} {p : Fin (n+1)} (hp : p ∈ A) :
    (delPosP A p).card = A.card - 1 := by
  rw [← Finset.card_erase_of_mem hp]
  refine Finset.card_bij (fun (t : Fin n) (_ : t ∈ delPosP A p) => Fin.succAbove p t) ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_erase]
    exact ⟨Fin.succAbove_ne p t, mem_delPosP.mp ht⟩
  · intro t1 _ t2 _ hh
    exact Fin.succAbove_right_injective hh
  · intro q hq
    rw [Finset.mem_erase] at hq
    obtain ⟨hq1, hq2⟩ := hq
    obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hq1
    exact ⟨t, mem_delPosP.mpr (by rw [ht]; exact hq2), ht⟩

lemma delPos_card {n : ℕ} {A : Finset (Fin (n+1))} {k : Fin (n+2)} (h : delIdx k ∈ A) :
    (delPos A k).card = A.card - 1 := by
  rw [delPos]
  exact delPosP_card h


/-! ### Insertion of a position -/

/-- Inserting a position `p` into a shuffle `A ⊆ Fin n`, giving a shuffle `⊆ Fin (n+1)`. -/
def insUp {n : ℕ} (A : Finset (Fin n)) (p : Fin (n+1)) : Finset (Fin (n+1)) :=
  A.image (Fin.succAbove p) ∪ {p}

lemma mem_insUp {n : ℕ} {A : Finset (Fin n)} {p : Fin (n+1)} {t : Fin (n+1)} :
    t ∈ insUp A p ↔ t = p ∨ ∃ t' ∈ A, Fin.succAbove p t' = t := by
  simp only [insUp, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro (⟨t', ht', rfl⟩ | rfl)
    · exact Or.inr ⟨t', ht', rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨t', ht', rfl⟩)
    · exact Or.inr rfl
    · exact Or.inl ⟨t', ht', rfl⟩

lemma insUp_card {n : ℕ} (A : Finset (Fin n)) (p : Fin (n+1)) :
    (insUp A p).card = A.card + 1 := by
  rw [insUp, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ Fin.succAbove_right_injective,
    Finset.card_singleton]
  rw [Finset.disjoint_singleton_right, Finset.mem_image]
  rintro ⟨t', _, ht'⟩
  exact Fin.succAbove_ne p t' ht'

/-- Inserting a position and deleting it again returns the original shuffle. -/
lemma delPosP_insUp {n : ℕ} (A : Finset (Fin n)) (p : Fin (n+1)) :
    delPosP (insUp A p) p = A := by
  ext t
  rw [mem_delPosP, mem_insUp]
  constructor
  · rintro (h | ⟨t', ht', h'⟩)
    · exact absurd h (Fin.succAbove_ne p t)
    · rwa [Fin.succAbove_right_injective h'] at ht'
  · intro ht
    exact Or.inr ⟨t, ht, rfl⟩

/-- Deleting a position of `A` and re-inserting it at the same position returns `A`. -/
lemma insUp_delPosP {n : ℕ} {A : Finset (Fin (n+1))} {p : Fin (n+1)} (hp : p ∈ A) :
    insUp (delPosP A p) p = A := by
  ext t
  rw [mem_insUp]
  constructor
  · rintro (rfl | ⟨t', ht', h'⟩)
    · exact hp
    · rw [← h']; exact mem_delPosP.mp ht'
  · intro ht
    by_cases h : t = p
    · exact Or.inl h
    · obtain ⟨t', ht'⟩ := Fin.exists_succAbove_eq h
      exact Or.inr ⟨t', mem_delPosP.mpr (by rw [ht']; exact ht), ht'⟩

/-! ### The shuffle maps at an explicit ambient degree -/

/-- The shuffle sign of `A`, as a generalisation of `shuffleSign`. -/
def invA {n : ℕ} (A : Finset (Fin n)) : ℕ :=
  A.sum fun i => ((Finset.univ \ A).filter fun j : Fin n => j.val < i.val).card

/-- The sign of the shuffle `A`. -/
def sgnA {n : ℕ} (A : Finset (Fin n)) : ℤ := (-1 : ℤ) ^ invA A

/-- The a-count map of a shuffle `A ⊆ Fin n` as a morphism `⦋n⦌ ⟶ ⦋p⦌`. -/
def shA {n p : ℕ} (A : Finset (Fin n)) (h : A.card ≤ p) : ⦋n⦌ ⟶ ⦋p⦌ :=
  SimplexCategory.mkHom
    { toFun := fun j => ⟨cnt A j.val, Nat.lt_succ_of_le (le_trans (cnt_le_card A _) h)⟩
      monotone' := fun i j hij => by
        simp only [Fin.mk_le_mk]
        exact cnt_mono A hij }

/-- The b-count map of a shuffle `A ⊆ Fin n` as a morphism `⦋n⦌ ⟶ ⦋q⦌`. -/
def shB {n q : ℕ} (A : Finset (Fin n)) (h : n ≤ A.card + q) : ⦋n⦌ ⟶ ⦋q⦌ :=
  SimplexCategory.mkHom
    { toFun := fun j => ⟨cntB A j.val, by
        have h2 : n - A.card ≤ q := by omega
        exact Nat.lt_succ_of_le (le_trans (cntB_le_card A j.val) h2)⟩
      monotone' := fun i j hij => by
        simp only [Fin.mk_le_mk]
        exact cntB_mono A hij }

lemma shA_apply_val {n p : ℕ} (A : Finset (Fin n)) (h : A.card ≤ p) (j : Fin (n+1)) :
    ((shA A h).toOrderHom j).val = cnt A j.val := rfl

lemma shB_apply_val {n q : ℕ} (A : Finset (Fin n)) (h : n ≤ A.card + q) (j : Fin (n+1)) :
    ((shB A h).toOrderHom j).val = cntB A j.val := rfl

end

end Work.Cohomology
