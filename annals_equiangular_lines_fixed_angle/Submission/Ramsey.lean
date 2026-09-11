import Mathlib

/-! Finite Ramsey theorem (two colours) with the exact consequence used for the
switching argument: every sufficiently large graph contains a large clique or a
large independent set.

Everything here is self-contained. -/

open Classical
open scoped BigOperators

namespace Submission.Ramsey

open Finset

/-- A Finset whose elements are pairwise adjacent. -/
def IsCliqueFinset {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ ⦃a : V⦄, a ∈ s → ∀ ⦃b : V⦄, b ∈ s → a ≠ b → G.Adj a b

/-- A Finset whose elements are pairwise non-adjacent. -/
def IsIndepFinset {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ ⦃a : V⦄, a ∈ s → ∀ ⦃b : V⦄, b ∈ s → a ≠ b → ¬ G.Adj a b

/-- `G` contains a clique of size at least `m`. -/
def HasClique {V : Type*} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ s : Finset V, m ≤ s.card ∧ IsCliqueFinset G s

/-- `G` contains an independent set of size at least `n`. -/
def HasIndep {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ s : Finset V, n ≤ s.card ∧ IsIndepFinset G s

/-- Inside the vertex set `U`, `G` contains a clique of size `m` or an independent set of
size `n`. -/
def RamOn {V : Type*} (G : SimpleGraph V) (U : Finset V) (m n : ℕ) : Prop :=
  (∃ s : Finset V, s ⊆ U ∧ m ≤ s.card ∧ IsCliqueFinset G s) ∨
    (∃ s : Finset V, s ⊆ U ∧ n ≤ s.card ∧ IsIndepFinset G s)

lemma isCliqueFinset_empty {V : Type*} (G : SimpleGraph V) : IsCliqueFinset G ∅ := by
  intro a ha; simp at ha

lemma isIndepFinset_empty {V : Type*} (G : SimpleGraph V) : IsIndepFinset G ∅ := by
  intro a ha; simp at ha

lemma isCliqueFinset_singleton {V : Type*} (G : SimpleGraph V) (a : V) :
    IsCliqueFinset G {a} := by
  intro x hx y hy hxy
  simp at hx hy
  subst x; subst y
  exact (hxy rfl).elim

lemma isIndepFinset_singleton {V : Type*} (G : SimpleGraph V) (a : V) :
    IsIndepFinset G {a} := by
  intro x hx y hy hxy
  simp at hx hy
  subst x; subst y
  exact (hxy rfl).elim

lemma isCliqueFinset_insert {V : Type*} (G : SimpleGraph V) {s : Finset V}
    (hs : IsCliqueFinset G s) {a : V} (h : ∀ b ∈ s, G.Adj a b) :
    IsCliqueFinset G (insert a s) := by
  intro x hx y hy hxy
  rw [mem_insert] at hx hy
  rcases hx with hxa | hxs
  · rcases hy with hya | hys
    · subst x; subst y; exact (hxy rfl).elim
    · subst x; exact h y hys
  · rcases hy with hya | hys
    · subst y; exact (G.adj_comm x a).mpr (h x hxs)
    · exact hs hxs hys hxy

lemma isIndepFinset_insert {V : Type*} (G : SimpleGraph V) {s : Finset V}
    (hs : IsIndepFinset G s) {a : V} (h : ∀ b ∈ s, ¬ G.Adj a b) :
    IsIndepFinset G (insert a s) := by
  intro x hx y hy hxy
  rw [mem_insert] at hx hy
  rcases hx with hxa | hxs
  · rcases hy with hya | hys
    · subst x; subst y; exact (hxy rfl).elim
    · subst x; exact h y hys
  · rcases hy with hya | hys
    · subst y
      intro hay
      exact h x hxs ((G.adj_comm x a).mp hay)
    · exact hs hxs hys hxy

/-- Splitting `U` at the vertex `u`: `u` contributes one element, the neighbours of `u`
in `U` the rest together with the non-neighbours. -/
private lemma split_card {V : Type*} (G : SimpleGraph V) (U : Finset V) (u : V)
    (hu : u ∈ U) :
    U.card =
      (U.filter fun w => G.Adj u w).card +
        (U.filter fun w => w ≠ u ∧ ¬G.Adj u w).card + 1 := by
  classical
  let N := U.filter fun w => G.Adj u w
  let M := U.filter fun w => w ≠ u ∧ ¬G.Adj u w
  have hUeq : U = insert u (N ∪ M) := by
    ext w
    constructor
    · intro hw
      by_cases hwu : w = u
      · simp [hwu]
      · by_cases hwadj : G.Adj u w
        · simp [N, hw, hwadj]
        · simp [M, hw, hwu, hwadj]
    · intro hw
      rw [mem_insert] at hw
      rcases hw with hwu | hwNM
      · exact hwu ▸ hu
      · rw [mem_union] at hwNM
        rcases hwNM with hwN | hwM
        · exact (Finset.filter_subset (fun w => G.Adj u w) U) hwN
        · exact (Finset.filter_subset (fun w => w ≠ u ∧ ¬G.Adj u w) U) hwM
  have huN : u ∉ N := by simp [N]
  have huM : u ∉ M := by simp [M]
  have hdisj : Disjoint N M := by
    rw [disjoint_left]
    intro a haN haM
    dsimp [N, M] at haN haM
    rw [mem_filter] at haN haM
    exact haM.2.2 haN.2
  calc
    U.card = (insert u (N ∪ M)).card := by rw [hUeq]
    _ = (N ∪ M).card + 1 := by
      rw [card_insert_of_notMem]
      intro h; exact (mem_union.mp h).elim huN huM
    _ = N.card + M.card + 1 := by rw [card_union_of_disjoint hdisj]
    _ = (U.filter (fun w => G.Adj u w)).card +
          (U.filter (fun w => w ≠ u ∧ ¬G.Adj u w)).card + 1 := by
      rfl

/-- Core induction: any set of `2 ^ e` vertices contains a clique of size `m` or an
independent set of size `n` whenever `m + n = e`. -/
private theorem ramsey_core : ∀ (e : ℕ), ∀ (m n : ℕ), m + n = e →
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (U : Finset V),
      2 ^ e ≤ U.card → RamOn G U m n := by
  intro e
  induction e with
  | zero =>
      intro m n hmn V hV G U hb
      left
      refine ⟨∅, by simp, ?_, isCliqueFinset_empty G⟩
      omega
  | succ e ih =>
      intro m n hmn V hV G U hb
      by_cases hm0 : m = 0
      · subst m
        left
        refine ⟨∅, by simp, ?_, isCliqueFinset_empty G⟩
        omega
      by_cases hn0 : n = 0
      · subst n
        right
        refine ⟨∅, by simp, ?_, isIndepFinset_empty G⟩
        omega
      have hm1 : 1 ≤ m := by omega
      have hn1 : 1 ≤ n := by omega
      by_cases hms : m = 1
      · -- a single vertex is a clique of size one
        have h1 : 1 ≤ 2 ^ (e + 1) := Nat.one_le_pow (e + 1) 2 (by norm_num)
        have hU : U.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : 0 < 1) h1) hb)
        rcases hU with ⟨u, hu⟩
        left
        refine ⟨{u}, ?_, ?_, isCliqueFinset_singleton G u⟩
        · intro x hx
          exact (mem_singleton.mp hx).symm ▸ hu
        · simp [hms]
      by_cases hns : n = 1
      · -- a single vertex is an independent set of size one
        have h1 : 1 ≤ 2 ^ (e + 1) := Nat.one_le_pow (e + 1) 2 (by norm_num)
        have hU : U.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : 0 < 1) h1) hb)
        rcases hU with ⟨u, hu⟩
        right
        refine ⟨{u}, ?_, ?_, isIndepFinset_singleton G u⟩
        · intro x hx
          exact (mem_singleton.mp hx).symm ▸ hu
        · simp [hns]
      -- now m ≥ 2 and n ≥ 2
      classical
      have h1 : 1 ≤ 2 ^ (e + 1) := Nat.one_le_pow (e + 1) 2 (by norm_num)
      have hU : U.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : 0 < 1) h1) hb)
      rcases hU with ⟨u, hu⟩
      let N : Finset V := U.filter fun w => G.Adj u w
      let M : Finset V := U.filter fun w => w ≠ u ∧ ¬G.Adj u w
      have hNsub : N ⊆ U := by
        intro w hw
        exact (mem_filter.mp hw).1
      have hMsub : M ⊆ U := by
        intro w hw
        exact (mem_filter.mp hw).1
      have huN : u ∉ N := by simp [N]
      have huM : u ∉ M := by simp [M]
      have hUcard : U.card = N.card + M.card + 1 := by
        simpa [N, M] using (split_card G U u hu)
      have hsplit : 2 ^ e ≤ N.card ∨ 2 ^ e ≤ M.card := by
        by_contra! h
        rw [pow_succ] at hb
        rw [mul_comm] at hb
        omega
      rcases hsplit with hN | hM
      · -- N side
        have hsumN : (m - 1) + n = e := by omega
        have hRamN : RamOn G N (m - 1) n := ih (m - 1) n hsumN V G N hN
        rcases hRamN with ⟨s, hsN, hcard1, hcl⟩ | ⟨s, hsN, hcard2, hind⟩
        · left
          refine ⟨insert u s, ?_, ?_, ?_⟩
          · rw [insert_subset_iff]
            exact ⟨hu, fun b hb => hNsub (hsN hb)⟩
          · have hus : u ∉ s := fun hm => huN (hsN hm)
            have hcard : (insert u s).card = s.card + 1 := card_insert_of_notMem hus
            omega
          · exact isCliqueFinset_insert G hcl (fun b hb => (mem_filter.mp (hsN hb)).2)
        · right
          refine ⟨s, ?_, hcard2, hind⟩
          intro b hb
          exact hNsub (hsN hb)
      · -- M side
        have hsumM : m + (n - 1) = e := by omega
        have hRamM : RamOn G M m (n - 1) := ih m (n - 1) hsumM V G M hM
        rcases hRamM with ⟨s, hsM, hcard1, hcl⟩ | ⟨s, hsM, hcard2, hind⟩
        · left
          refine ⟨s, ?_, hcard1, hcl⟩
          intro b hb
          exact hMsub (hsM hb)
        · right
          refine ⟨insert u s, ?_, ?_, ?_⟩
          · rw [insert_subset_iff]
            exact ⟨hu, fun b hb => hMsub (hsM hb)⟩
          · have hus : u ∉ s := fun hm => huM (hsM hm)
            have hcard : (insert u s).card = s.card + 1 := card_insert_of_notMem hus
            omega
          · exact isIndepFinset_insert G hind (fun b hb => (mem_filter.mp (hsM hb)).2.2)

/-- The two-colour Ramsey number `R(m,n)` exists: every graph on `R(m,n)` vertices
contains a clique of size `m` or an independent set of size `n`. -/
theorem ramsey_clique_indep (m n : ℕ) :
    ∃ R : ℕ, ∀ (V : Type) [Fintype V], R ≤ Fintype.card V →
      ∀ G : SimpleGraph V,
        (∃ s : Finset V, m ≤ s.card ∧ ∀ ⦃a : V⦄, a ∈ s → ∀ ⦃b : V⦄, b ∈ s → a ≠ b → G.Adj a b) ∨
        (∃ s : Finset V, n ≤ s.card ∧ ∀ ⦃a : V⦄, a ∈ s → ∀ ⦃b : V⦄, b ∈ s → a ≠ b → ¬ G.Adj a b) := by
  classical
  refine ⟨2 ^ (m + n), ?_⟩
  intro V hV hR G
  have hc : RamOn G (Finset.univ : Finset V) m n :=
    ramsey_core (m + n) m n (by rfl) V G (Finset.univ : Finset V) (by simpa [Finset.card_univ] using hR)
  rcases hc with ⟨s, hsub, hcard, hcl⟩ | ⟨s, hsub, hcard, hind⟩
  · left
    exact ⟨s, hcard, hcl⟩
  · right
    exact ⟨s, hcard, hind⟩

end Submission.Ramsey
