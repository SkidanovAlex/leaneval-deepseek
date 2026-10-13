/-
  WilG2 : the combinatorial core for `ofp_weighted_sum`.

  Given a family `B : Fin k → Finset (Fin m)` of nonempty pairwise disjoint blocks covering
  `Fin m`, `ofpOfBlocks B ...` is the `OrderedFinpartition` whose parts are the `B i`, ordered
  by increasing maximum; `sortPerm B ...` is the permutation of the index set sending a block to
  its position in that order.  This "sorting" construction is what relates Mathlib's
  `OrderedFinpartition` (the index type of Faà di Bruno) to partitions of `Fin m` given as a
  labelled family of blocks, and hence to `Composition m`.
-/
import Mathlib

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.WilG2

/-! ### Fibers of a function -/

/-- The fiber of `f` over `i`. -/
def fib {m k : ℕ} (f : Fin m → Fin k) (i : Fin k) : Finset (Fin m) :=
  univ.filter fun j => f j = i

@[simp] lemma mem_fib {m k : ℕ} {f : Fin m → Fin k} {i : Fin k} {j : Fin m} :
    j ∈ fib f i ↔ f j = i := by
  simp [fib]

lemma fib_nonempty {m k : ℕ} {f : Fin m → Fin k} (hf : Function.Surjective f) (i : Fin k) :
    (fib f i).Nonempty := by
  obtain ⟨j, hj⟩ := hf i
  exact ⟨j, mem_fib.mpr hj⟩

lemma fib_disjoint {m k : ℕ} (f : Fin m → Fin k) {i i' : Fin k} (h : i ≠ i') :
    Disjoint (fib f i) (fib f i') := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  rw [mem_fib] at hj hj'
  exact h (hj.symm.trans hj')

lemma fib_cover {m k : ℕ} (f : Fin m → Fin k) (j : Fin m) : ∃ i, j ∈ fib f i :=
  ⟨f j, mem_fib.mpr rfl⟩

/-! ### Ranking blocks by their maximum -/

section Rank

variable {m k : ℕ}

/-- `rankF mx i` is the number of indices whose `mx`-value is smaller than `mx i`, i.e. the
position of `i` in the ordering of `Fin k` by increasing `mx`-values (when `mx` is injective). -/
def rankF (mx : Fin k → Fin m) (i : Fin k) : ℕ :=
  (univ.filter fun i' => mx i' < mx i).card

lemma rankF_lt_iff {mx : Fin k → Fin m} (hinj : Function.Injective mx) (i i' : Fin k) :
    rankF mx i < rankF mx i' ↔ mx i < mx i' := by
  have hle : ∀ ⦃a b : Fin k⦄, mx a < mx b →
      (univ.filter fun i'' => mx i'' < mx a) ⊆ (univ.filter fun i'' => mx i'' < mx b) := by
    intro a b hab i'' hi''
    simp only [mem_filter, mem_univ, true_and] at hi'' ⊢
    exact lt_trans hi'' hab
  constructor
  · intro h
    by_contra hc
    have hba : mx i' < mx i := lt_of_le_of_ne (le_of_not_gt hc)
      (fun heq => absurd h (by rw [hinj heq]; exact lt_irrefl _))
    have := card_le_card (hle hba)
    simp only [rankF] at h ⊢
    omega
  · intro h
    have hss : (univ.filter fun i'' => mx i'' < mx i) ⊂
        (univ.filter fun i'' => mx i'' < mx i') := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨hle h, fun heq => ?_⟩
      have hi : i ∈ univ.filter fun i'' => mx i'' < mx i' := by simp [h]
      rw [← heq] at hi
      simp at hi
    have := card_lt_card hss
    simpa only [rankF] using this

lemma rankF_lt {mx : Fin k → Fin m} (i : Fin k) : rankF mx i < k := by
  rw [rankF]
  have hsub : (univ.filter fun i' => mx i' < mx i) ⊆ (univ : Finset (Fin k)) := subset_univ _
  have hne : (univ.filter fun i' => mx i' < mx i) ≠ (univ : Finset (Fin k)) := by
    intro heq
    have : i ∈ univ.filter (fun i' => mx i' < mx i) := by rw [heq]; exact mem_univ i
    simp at this
  have := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  simpa using this

lemma rankF_injective {mx : Fin k → Fin m} (hinj : Function.Injective mx) :
    Function.Injective (rankF mx) := by
  intro i i' h
  by_contra hne
  have hne' : mx i ≠ mx i' := fun hh => hne (hinj hh)
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · exact absurd h (ne_of_lt ((rankF_lt_iff hinj i i').mpr hlt))
  · exact absurd h.symm (ne_of_lt ((rankF_lt_iff hinj i' i).mpr hlt))

end Rank

/-- The last value of the increasing enumeration of a finset is its maximum. -/
lemma orderEmbOfFin_last' {α : Type*} [LinearOrder α] {s : Finset α} {n : ℕ}
    (h : s.card = n) {i : Fin n} (hi : (i : ℕ) = n - 1) (hs : s.Nonempty) :
    s.orderEmbOfFin h i = s.max' hs := by
  have hz : 0 < n := by omega
  have hone : i = ⟨n - 1, Nat.sub_lt hz (Nat.succ_pos 0)⟩ := Fin.ext hi
  rw [hone, Finset.orderEmbOfFin_last h hz]

/-! ### Sorting a family of blocks by increasing maximum -/

section Blocks

variable {m k : ℕ}

lemma blockMax_injective (B : Fin k → Finset (Fin m)) (hne : ∀ i, (B i).Nonempty)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i')) :
    Function.Injective fun i => (B i).max' (hne i) := by
  intro i i' h
  change (B i).max' (hne i) = (B i').max' (hne i') at h
  by_contra hne'
  have h1 : (B i).max' (hne i) ∈ B i' := by
    rw [h]
    exact (B i').max'_mem _
  exact (Finset.disjoint_left.mp (hdisj i i' hne')) ((B i).max'_mem _) h1

/-- For a family of nonempty pairwise disjoint blocks `B : Fin k → Finset (Fin m)`, the
permutation of the index set sending `i` to the position of `B i` in the order of increasing
maximum. -/
@[reducible] def sortPerm (B : Fin k → Finset (Fin m)) (hne : ∀ i, (B i).Nonempty)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i')) : Equiv.Perm (Fin k) :=
  Equiv.ofBijective (fun i : Fin k =>
      (⟨rankF (fun i => (B i).max' (hne i)) i, rankF_lt i⟩ : Fin k))
    ⟨fun _ _ h => rankF_injective (blockMax_injective B hne hdisj) (congrArg Fin.val h),
      Finite.injective_iff_surjective.mp
        (fun _ _ h => rankF_injective (blockMax_injective B hne hdisj) (congrArg Fin.val h))⟩

@[simp] lemma sortPerm_apply (B : Fin k → Finset (Fin m)) (hne : ∀ i, (B i).Nonempty)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i')) (i : Fin k) :
    (sortPerm B hne hdisj i : ℕ) = rankF (fun i => (B i).max' (hne i)) i := rfl

/-- The maximum of the `p`-th block in the increasing-maximum order is strictly increasing. -/
lemma blockMax_sortPerm_symm_strictMono (B : Fin k → Finset (Fin m))
    (hne : ∀ i, (B i).Nonempty) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i')) :
    StrictMono fun p : Fin k => (B ((sortPerm B hne hdisj).symm p)).max' (hne _) := by
  intro p q hpq
  refine (rankF_lt_iff (blockMax_injective B hne hdisj) _ _).mp ?_
  have h1 : rankF (fun i => (B i).max' (hne i)) ((sortPerm B hne hdisj).symm p) = (p : ℕ) := by
    rw [← sortPerm_apply B hne hdisj, Equiv.apply_symm_apply]
  have h2 : rankF (fun i => (B i).max' (hne i)) ((sortPerm B hne hdisj).symm q) = (q : ℕ) := by
    rw [← sortPerm_apply B hne hdisj, Equiv.apply_symm_apply]
  rw [h1, h2]
  simpa using hpq

/-- The ordered finpartition whose parts are the blocks `B`, ordered by increasing maximum:
the `p`-th part is `B ((sortPerm B hne hdisj).symm p)`. -/
@[reducible] def ofpOfBlocks (B : Fin k → Finset (Fin m)) (hne : ∀ i, (B i).Nonempty)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    (hcover : ∀ j : Fin m, ∃ i : Fin k, j ∈ B i) : OrderedFinpartition m where
  length := k
  partSize p := (B ((sortPerm B hne hdisj).symm p)).card
  partSize_pos p := card_pos.mpr (hne _)
  emb p := (B ((sortPerm B hne hdisj).symm p)).orderEmbOfFin rfl
  emb_strictMono p := ((B ((sortPerm B hne hdisj).symm p)).orderEmbOfFin rfl).strictMono
  parts_strictMono := by
    intro p q hpq
    show (B ((sortPerm B hne hdisj).symm p)).orderEmbOfFin rfl
        ⟨(B ((sortPerm B hne hdisj).symm p)).card - 1, _⟩ <
      (B ((sortPerm B hne hdisj).symm q)).orderEmbOfFin rfl
        ⟨(B ((sortPerm B hne hdisj).symm q)).card - 1, _⟩
    rw [orderEmbOfFin_last' (s := B ((sortPerm B hne hdisj).symm p)) rfl rfl (hne _),
      orderEmbOfFin_last' (s := B ((sortPerm B hne hdisj).symm q)) rfl rfl (hne _)]
    exact blockMax_sortPerm_symm_strictMono B hne hdisj hpq
  disjoint := by
    rw [Set.pairwiseDisjoint_iff]
    intro i _ j _ hij
    rw [Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin] at hij
    by_contra h
    have hd := hdisj ((sortPerm B hne hdisj).symm i) ((sortPerm B hne hdisj).symm j)
      (fun hh => h ((sortPerm B hne hdisj).symm.injective hh))
    have h2 : (↑(B ((sortPerm B hne hdisj).symm i)) ∩
        ↑(B ((sortPerm B hne hdisj).symm j)) : Set (Fin m)) = ∅ := by
      rw [← Finset.coe_inter, Finset.coe_eq_empty]
      exact Finset.disjoint_iff_inter_eq_empty.mp hd
    rw [h2] at hij
    exact Set.not_nonempty_empty hij
  cover x := by
    obtain ⟨i, hi⟩ := hcover x
    refine ⟨sortPerm B hne hdisj i, ?_⟩
    rw [Finset.range_orderEmbOfFin, Equiv.symm_apply_apply]
    exact hi

@[simp] lemma range_emb_ofpOfBlocks (B : Fin k → Finset (Fin m)) (hne : ∀ i, (B i).Nonempty)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    (hcover : ∀ j : Fin m, ∃ i : Fin k, j ∈ B i) (p : Fin k) :
    Set.range ((ofpOfBlocks B hne hdisj hcover).emb p) =
      (B ((sortPerm B hne hdisj).symm p) : Set (Fin m)) := by
  show Set.range ((B ((sortPerm B hne hdisj).symm p)).orderEmbOfFin rfl) = _
  rw [Finset.range_orderEmbOfFin]

@[simp] lemma length_ofpOfBlocks (B : Fin k → Finset (Fin m)) (hne : ∀ i, (B i).Nonempty)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    (hcover : ∀ j : Fin m, ∃ i : Fin k, j ∈ B i) :
    (ofpOfBlocks B hne hdisj hcover).length = k := rfl

@[simp] lemma partSize_ofpOfBlocks (B : Fin k → Finset (Fin m)) (hne : ∀ i, (B i).Nonempty)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    (hcover : ∀ j : Fin m, ∃ i : Fin k, j ∈ B i) (p : Fin k) :
    (ofpOfBlocks B hne hdisj hcover).partSize p = (B ((sortPerm B hne hdisj).symm p)).card := rfl

end Blocks

end Work.WilG2
