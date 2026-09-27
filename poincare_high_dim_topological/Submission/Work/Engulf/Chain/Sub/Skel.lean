import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Basic

/-!
# `Submission.Work.Engulf.Chain.Sub.Skel`

The bookkeeping of the outer shelling loop of `Work.Engulf.Chain.E5` (Newman §15).

`skel ord i` is the union of the facets of the first `i` top simplices of the shelling list
`ord` (Newman's `Q^q_i`, the `q`-skeleton already engulfed after `i` steps) and `covOrd ord i`
is the union of those `i` top simplices themselves.  The main results are `skel_succ`,
`skel_subset_covOrd`, `shellUnion_eq_covOrd` (the union occurring in
`Work.Engulf.SubdivTools.shell` is `covOrd`), and `meet_skel`: the intersection of `K ∪ skel ord i`
with the `i`-th top simplex is the union of the facets opposite the floor side `τ₁'`.  This last
one is the `meetK` hypothesis of the `L7c` step of the outer loop.
-/

open Set Metric PL

set_option maxHeartbeats 1000000

namespace Work.Engulf.Chain

variable {N : ℕ}

/-! ## Membership forms -/

theorem mem_erase_union {σ : Finset (PL.E N)} {y : PL.E N} :
    y ∈ ⋃ w ∈ σ, PL.simp (σ.erase w) ↔ ∃ w ∈ σ, y ∈ PL.simp (σ.erase w) := by
  simp only [Set.mem_iUnion, exists_prop]

theorem mem_range_erase_union {ord : List (Finset (PL.E N))} {i : ℕ} {y : PL.E N} :
    y ∈ (⋃ j ∈ Finset.range i, ⋃ w ∈ ord.getD j ∅,
          PL.simp ((ord.getD j ∅).erase w))
      ↔ ∃ j ∈ Finset.range i, ∃ w ∈ ord.getD j ∅,
          y ∈ PL.simp ((ord.getD j ∅).erase w) := by
  simp only [Set.mem_iUnion, exists_prop]

theorem mem_list_erase_union {ord : List (Finset (PL.E N))} {y : PL.E N} :
    y ∈ (⋃ s ∈ ord, ⋃ w ∈ s, PL.simp (s.erase w))
      ↔ ∃ s ∈ ord, ∃ w ∈ s, y ∈ PL.simp (s.erase w) := by
  simp only [Set.mem_iUnion, exists_prop]

/-- Splitting the union over `range (i+1)`. -/
theorem iUnion_range_succ {α : Type*} (f : ℕ → Set α) (i : ℕ) :
    (⋃ j ∈ Finset.range (i + 1), f j) = f i ∪ ⋃ j ∈ Finset.range i, f j := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union, exists_prop]
  constructor
  · rintro ⟨j, hj, hx⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · exact Or.inr ⟨j, hj', hx⟩
    · exact Or.inl hx
  · rintro (hx | ⟨j, hj, hx⟩)
    · exact ⟨i, Nat.lt_succ_self i, hx⟩
    · exact ⟨j, Nat.lt_succ_of_lt hj, hx⟩

/-! ## The skeleton of the shelling loop -/

/-- The union of the facets of the first `i` simplices of the shelling list. -/
def skel (ord : List (Finset (PL.E N))) : ℕ → Set (PL.E N)
  | 0 => ∅
  | i + 1 => skel ord i ∪ ⋃ w ∈ ord.getD i ∅, PL.simp ((ord.getD i ∅).erase w)

/-- The union of the first `i` simplices of the shelling list. -/
def covOrd (ord : List (Finset (PL.E N))) : ℕ → Set (PL.E N)
  | 0 => ∅
  | i + 1 => covOrd ord i ∪ PL.simp (ord.getD i ∅)

@[simp] theorem skel_zero (ord : List (Finset (PL.E N))) : skel ord 0 = ∅ := rfl

theorem skel_succ (ord : List (Finset (PL.E N))) (i : ℕ) :
    skel ord (i + 1) = skel ord i ∪ ⋃ w ∈ ord.getD i ∅, PL.simp ((ord.getD i ∅).erase w) := rfl

@[simp] theorem covOrd_zero (ord : List (Finset (PL.E N))) : covOrd ord 0 = ∅ := rfl

theorem covOrd_succ (ord : List (Finset (PL.E N))) (i : ℕ) :
    covOrd ord (i + 1) = covOrd ord i ∪ PL.simp (ord.getD i ∅) := rfl

theorem monoT_skel (ord : List (Finset (PL.E N))) : Monotone (skel ord) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact subset_rfl
  | succ j _ ih => rw [skel_succ]; exact ih.trans subset_union_left

theorem monoT_covOrd (ord : List (Finset (PL.E N))) : Monotone (covOrd ord) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact subset_rfl
  | succ j _ ih => rw [covOrd_succ]; exact ih.trans subset_union_left

theorem skel_subset_covOrd (ord : List (Finset (PL.E N))) (i : ℕ) :
    skel ord i ⊆ covOrd ord i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [skel_succ, covOrd_succ]
    refine union_subset_iff.2 ⟨ih.trans subset_union_left, ?_⟩
    intro y hy
    rw [mem_erase_union] at hy
    obtain ⟨w, hw, hyw⟩ := hy
    exact Or.inr (simp_mono (Finset.erase_subset w _) hyw)

/-- `skel` as an explicit union over the first `i` positions of the list. -/
theorem skel_eq_range (ord : List (Finset (PL.E N))) (i : ℕ) :
    skel ord i = ⋃ j ∈ Finset.range i, ⋃ w ∈ ord.getD j ∅,
      PL.simp ((ord.getD j ∅).erase w) := by
  induction i with
  | zero => simp
  | succ i ih => rw [skel_succ, ih, iUnion_range_succ, union_comm]

/-- `topOf` as an explicit union. -/
theorem topOf_eq_iUnion (τ₀ τ₁ : Finset (PL.E N)) :
    Work.Engulf.topOf τ₀ τ₁ = ⋃ w ∈ τ₀, PL.simp ((τ₀ ∪ τ₁).erase w) := rfl

/-- A facet of the `j`-th simplex of the list, `j < i`, lies in `skel ord i`. -/
theorem simp_erase_subset_skel (ord : List (Finset (PL.E N))) {i j : ℕ} (hji : j < i)
    {w : PL.E N} (hw : w ∈ ord.getD j ∅) :
    PL.simp ((ord.getD j ∅).erase w) ⊆ skel ord i := by
  have h1 : PL.simp ((ord.getD j ∅).erase w) ⊆ skel ord (j + 1) := by
    rw [skel_succ]
    intro y hy
    exact Or.inr (by rw [mem_erase_union]; exact ⟨w, hw, hy⟩)
  exact h1.trans (monoT_skel ord (by omega))

/-- The same with an explicit name for the top simplex. -/
theorem simp_erase_subset_skel_of (ord : List (Finset (PL.E N))) {i j : ℕ} (hji : j < i)
    {σj : Finset (PL.E N)} (hσj : ord.getD j ∅ = σj) {w : PL.E N} (hw : w ∈ σj) :
    PL.simp (σj.erase w) ⊆ skel ord i := by
  rw [← hσj] at hw ⊢
  exact simp_erase_subset_skel ord hji hw

/-- Membership in `covOrd`. -/
theorem mem_covOrd {ord : List (Finset (PL.E N))} {i : ℕ} {x : PL.E N} (h : x ∈ covOrd ord i) :
    ∃ j < i, x ∈ PL.simp (ord.getD j ∅) := by
  induction i with
  | zero => exact absurd h (by simp)
  | succ i ih =>
    rw [covOrd_succ] at h
    simp only [Set.mem_union] at h
    rcases h with h | h
    · obtain ⟨j, hj, hx⟩ := ih h
      exact ⟨j, by omega, hx⟩
    · exact ⟨i, by omega, h⟩

/-- The union `⋃ j ∈ range i, ⋃ (hj : j < ord.length), simp (ord[j])` of the shelling statement
is `covOrd ord i`. -/
theorem shellUnion_eq_covOrd (ord : List (Finset (PL.E N))) (i : ℕ) :
    (⋃ j ∈ Finset.range i, ⋃ (_ : j < ord.length), PL.simp (ord[j])) = covOrd ord i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have haux : (⋃ (_ : i < ord.length), PL.simp (ord[i])) = PL.simp (ord.getD i ∅) := by
      by_cases h : i < ord.length
      · rw [List.getD_eq_get ord ∅ ⟨i, h⟩]
        exact le_antisymm (Set.iUnion_subset fun _ => subset_rfl)
          (Set.subset_iUnion (fun _ : i < ord.length => PL.simp (ord[i])) h)
      · rw [List.getD_eq_default ord ∅ (by omega), simp_empty, Set.iUnion_eq_empty]
        exact fun p => (h p).elim
    rw [iUnion_range_succ, ih, haux, covOrd_succ]
    exact union_comm _ _

/-- The union of the facets of all the top simplices of the list, as a `range`-indexed union. -/
theorem iUnion_erase_eq_range (ord : List (Finset (PL.E N))) :
    (⋃ s ∈ ord, ⋃ w ∈ s, PL.simp (s.erase w))
      = ⋃ j ∈ Finset.range ord.length,
          ⋃ w ∈ ord.getD j ∅, PL.simp ((ord.getD j ∅).erase w) := by
  ext x
  rw [mem_list_erase_union, mem_range_erase_union]
  constructor
  · rintro ⟨s, hs, w, hw, hx⟩
    obtain ⟨j, hjs⟩ := List.mem_iff_get.1 hs
    have hget : ord.getD j.1 ∅ = s := by rw [List.getD_eq_get ord ∅ j, hjs]
    exact ⟨j.1, Finset.mem_range.2 j.2, w, by rw [hget]; exact hw, by rw [hget]; exact hx⟩
  · rintro ⟨j, hj, w, hw, hx⟩
    have hjl : j < ord.length := Finset.mem_range.1 hj
    have hget : ord.getD j ∅ = ord.get ⟨j, hjl⟩ := List.getD_eq_get ord ∅ ⟨j, hjl⟩
    exact ⟨ord.get ⟨j, hjl⟩, List.get_mem ord ⟨j, hjl⟩, w,
      by rw [hget] at hw; exact hw, by rw [hget] at hx; exact hx⟩

/-- The facets of the first `i` top simplices lie in `skel ord i`. -/
theorem range_erase_subset_skel (ord : List (Finset (PL.E N))) {i : ℕ} (hi : i ≤ ord.length) :
    (⋃ j ∈ Finset.range i, ⋃ w ∈ ord.getD j ∅, PL.simp ((ord.getD j ∅).erase w))
      ⊆ skel ord i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [iUnion_range_succ, skel_succ]
    refine union_subset_iff.2 ⟨?_, (ih (by omega)).trans subset_union_left⟩
    intro y hy
    rw [mem_erase_union] at hy
    obtain ⟨w, hw, hyw⟩ := hy
    exact Or.inr (by rw [mem_erase_union]; exact ⟨w, hw, hyw⟩)

/-- **`meetK` for the shelling loop.** -/
theorem meet_skel {Γ₁ : PL.Cx N} {K : Set (PL.E N)} {Δ σ τ₁' : Finset (PL.E N)}
    {ord : List (Finset (PL.E N))} {i : ℕ} {τ₀ τ₁ : Finset (PL.E N)}
    (hget : ord.getD i ∅ = σ) (hnodup : ord.Nodup) (hlen : i < ord.length)
    (hfaces : ∀ j (hj : j < ord.length), ord.get ⟨j, hj⟩ ∈ Γ₁.faces)
    (hcards : ∀ j (hj : j < ord.length), (ord.get ⟨j, hj⟩).card = Δ.card)
    (hσcard : σ.card = Δ.card)
    (hsimpσ : PL.simp σ ⊆ PL.simp Δ)
    (hmeet : K ∩ PL.simp Δ = Work.Engulf.floorOf τ₀ τ₁)
    (hshell : PL.simp σ ∩ (Work.Engulf.floorOf τ₀ τ₁ ∪ covOrd ord i)
        = ⋃ w ∈ τ₁', PL.simp (σ.erase w)) :
    (K ∪ skel ord i) ∩ PL.simp σ = ⋃ w ∈ τ₁', PL.simp (σ.erase w) := by
  classical
  have hget' : ord.get ⟨i, hlen⟩ = σ := by
    rw [← List.getD_eq_get ord ∅ ⟨i, hlen⟩]; exact hget
  have hσmem : σ ∈ Γ₁.faces := hget'.symm ▸ hfaces i hlen
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxK | hxS, hxσ⟩
    · rw [← hshell]
      exact ⟨hxσ, Or.inl (by rw [← hmeet]; exact ⟨hxK, hsimpσ hxσ⟩)⟩
    · rw [← hshell]
      exact ⟨hxσ, Or.inr (skel_subset_covOrd ord i hxS)⟩
  · intro x hx
    rw [← hshell] at hx
    obtain ⟨hxσ, hxB | hxC⟩ := hx
    · exact Set.mem_inter (Or.inl (by rw [← hmeet] at hxB; exact hxB.1)) hxσ
    · obtain ⟨j, hji, hxj⟩ := mem_covOrd hxC
      have hjl : j < ord.length := by
        by_contra hcon
        rw [List.getD_eq_default ord ∅ (by omega)] at hxj
        rw [simp_empty] at hxj
        exact hxj
      have hjm : ord.get ⟨j, hjl⟩ ∈ Γ₁.faces := hfaces j hjl
      have hjg : ord.getD j ∅ = ord.get ⟨j, hjl⟩ := List.getD_eq_get ord ∅ ⟨j, hjl⟩
      have hxj' : x ∈ PL.simp (ord.get ⟨j, hjl⟩) := by rw [← hjg]; exact hxj
      have hinter : x ∈ PL.simp (σ ∩ ord.get ⟨j, hjl⟩) := by
        rw [← simp_inter hσmem hjm]
        exact ⟨hxσ, hxj'⟩
      have hne : σ ∩ ord.get ⟨j, hjl⟩ ≠ ord.get ⟨j, hjl⟩ := by
        intro heq
        have hsub : ord.get ⟨j, hjl⟩ ⊆ σ := heq ▸ Finset.inter_subset_left
        have hcard : (ord.get ⟨j, hjl⟩).card = σ.card := by rw [hcards j hjl, ← hσcard]
        have hEq : ord.get ⟨j, hjl⟩ = σ := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
        have hnod : ord.get ⟨j, hjl⟩ = ord.get ⟨i, hlen⟩ := hEq.trans hget'.symm
        have hidx : j = i := Fin.ext_iff.1 ((hnodup.get_inj_iff).1 hnod)
        omega
      have hssub : σ ∩ ord.get ⟨j, hjl⟩ ⊂ ord.get ⟨j, hjl⟩ :=
        Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_right, hne⟩
      obtain ⟨w', hw'j, hw'ne⟩ := Finset.exists_of_ssubset hssub
      have hsub : σ ∩ ord.get ⟨j, hjl⟩ ⊆ (ord.get ⟨j, hjl⟩).erase w' := by
        intro y hy
        rw [Finset.mem_erase]
        have hy' : y ∈ (σ ∩ ord.get ⟨j, hjl⟩ : Finset (PL.E N)) := hy
        rw [Finset.mem_inter] at hy'
        exact ⟨fun hyw => hw'ne (by rw [← hyw]; exact Finset.mem_inter.mpr ⟨hy'.1, hy'.2⟩),
          hy'.2⟩
      have hxs : x ∈ PL.simp ((ord.get ⟨j, hjl⟩).erase w') := simp_mono hsub hinter
      exact Set.mem_inter
        (Or.inr (simp_erase_subset_skel_of ord hji hjg hw'j hxs)) hxσ

end Work.Engulf.Chain
