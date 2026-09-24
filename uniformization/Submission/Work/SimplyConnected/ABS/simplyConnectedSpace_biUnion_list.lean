import Mathlib
import Submission.Work.SimplyConnected.ABS.simplyConnectedSpace_of_isOpen_union

namespace Work.SimplyConnected.ABS

open Set

/-! ## A local refinement of the `omega` tactic

The statement requested for `simplyConnectedSpace_biUnion_list` (below) is written with the
*accumulated* union `⋃ i ∈ Finset.range (k + 1), l.get ⟨i, …⟩`, and the natural proof that the
index is `< l.length` is `by omega`, using

* `i ∈ Finset.range (k + 1)` — the hypothesis introduced by the `⋃ i ∈ ⋯` binder, and
* `hk : k + 1 < l.length` — a hypothesis of the statement.

The difficulty is that `omega` does not preprocess `Finset`-membership hypotheses: it only sees
`Nat`/`Int` comparisons (see `Lean.Elab.Tactic.Omega.addFact`), so a bare `by omega` cannot
discharge that `Fin` bound.  The two declarations below repair exactly this gap: `omegaFinset`
first calls `omega`, and if that fails it rewrites `Finset`-membership hypotheses into
`Nat` comparisons and calls `omega` again.  The macro rule is `local`, so it is in force only
inside the section below and does not affect any other file. -/

section OmegaRangeMembership

open Lean Elab Tactic in
/-- The builtin `omega` tactic, callable from inside a `macro_rules` override of `omega`. -/
elab "omegaBuiltin" : tactic => do
  Lean.Elab.Tactic.Omega.evalOmega (← `(tactic| omega))

/-- `omega`, first simplifying `Finset`-membership hypotheses into `Nat` comparisons. -/
macro "omegaFinset" : tactic =>
  `(tactic| first
      | omegaBuiltin
      | (simp only [Finset.mem_range, Finset.mem_singleton, Set.mem_Iio, Set.mem_Ici,
            Set.mem_Icc] at *
         omegaBuiltin))

local macro_rules | `(tactic| omega) => `(tactic| omegaFinset)

/-- The union of the first `n` members of a list of sets, with the `i`-th member read through
`List.getD · ∅` so that no proof of `i < l.length` is needed. -/
private def accUnion {X : Type*} (l : List (Set X)) (n : ℕ) : Set X :=
  ⋃ i ∈ Finset.range n, l.getD i ∅

private lemma accUnion_apply {X : Type*} (l : List (Set X)) (n : ℕ) :
    accUnion l n = ⋃ i ∈ Finset.range n, l.getD i ∅ := rfl

private lemma getD_eq_get_of_lt {X : Type*} (l : List (Set X)) {i : ℕ} (h : i < l.length) :
    l.getD i ∅ = l.get ⟨i, h⟩ := List.getD_eq_get l ∅ ⟨i, h⟩

/-- One more member: the accumulated union of the first `n + 1` members is the accumulated union of
the first `n` members together with the `n`-th member. -/
private lemma accUnion_union {X : Type*} (l : List (Set X)) (n : ℕ) :
    accUnion l (n + 1) = accUnion l n ∪ l.getD n ∅ := by
  simp only [accUnion_apply]
  ext x
  simp only [Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi, hx⟩
    rw [Finset.mem_range] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact Or.inl ⟨i, by rw [Finset.mem_range]; exact h, hx⟩
    · exact Or.inr (h ▸ hx)
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, by rw [Finset.mem_range]; rw [Finset.mem_range] at hi; omega, hx⟩
    · exact ⟨n, by rw [Finset.mem_range]; omega, hx⟩

/-- The accumulated union of the first `m` members, written as the union of the members themselves
(as in the hypothesis `hpc` of the main statement). -/
private lemma accUnion_eq_iUnion_get {X : Type*} (l : List (Set X)) {m : ℕ}
    (hm : m ≤ l.length) :
    accUnion l m = ⋃ i ∈ Finset.range m, l.get ⟨i, by omega⟩ := by
  simp only [accUnion_apply]
  apply Set.iUnion_congr
  intro i
  apply Set.iUnion_congr
  intro hi
  exact getD_eq_get_of_lt (i := i) l (by omega)

/-- **A chain of simply connected open sets has a simply connected union.**

If `l` is a non-empty list of open subsets of a topological space, each simply connected, and for
every `k` the intersection of the *accumulated* union `⋃ i ≤ k, l[i]` with the next member
`l[k+1]` is path connected, then `⋃ B ∈ l, B` is simply connected.  (By induction with the
van Kampen/`simplyConnectedSpace_of_isOpen_union` step.) -/
theorem simplyConnectedSpace_biUnion_list {X : Type*} [TopologicalSpace X]
    (l : List (Set X)) (hne : l ≠ []) (hopen : ∀ B ∈ l, IsOpen B)
    (hsc : ∀ B ∈ l, SimplyConnectedSpace ↥B)
    (hpc : ∀ (k : ℕ) (hk : k + 1 < l.length),
      PathConnectedSpace
        ↥((⋃ i ∈ Finset.range (k + 1), l.get ⟨i, by omega⟩) ∩ l.get ⟨k + 1, by omega⟩)) :
    SimplyConnectedSpace ↥(⋃ B ∈ l, (B : Set X)) := by
  classical
  have hOpenGetD : ∀ i, IsOpen (l.getD i ∅) := by
    intro i
    by_cases h : i < l.length
    · rw [getD_eq_get_of_lt l h]
      exact hopen _ (List.get_mem l ⟨i, h⟩)
    · rw [List.getD_eq_default l ∅ (by omega)]
      exact isOpen_empty
  have hOpenAcc : ∀ n, IsOpen (accUnion l n) := by
    intro n
    rw [accUnion_apply]
    exact isOpen_biUnion (fun i _ => hOpenGetD i)
  have hSCGetD : ∀ i, i < l.length → SimplyConnectedSpace ↥(l.getD i ∅) := by
    intro i h
    rw [getD_eq_get_of_lt l h]
    exact hsc _ (List.get_mem l ⟨i, h⟩)
  have hPC : ∀ (k : ℕ) (hk : k + 1 < l.length),
      PathConnectedSpace ↥(accUnion l (k + 1) ∩ l.getD (k + 1) ∅) := by
    intro k hk
    have h1 := accUnion_eq_iUnion_get l (m := k + 1) (by omega)
    have h2 : l.getD (k + 1) ∅ = l.get ⟨k + 1, hk⟩ := getD_eq_get_of_lt l hk
    rw [h1, h2]
    exact hpc k hk
  have key : ∀ n, n + 1 ≤ l.length → SimplyConnectedSpace ↥(accUnion l (n + 1)) := by
    intro n
    induction n with
    | zero =>
        intro _
        have h0 : 0 < l.length := List.length_pos_of_ne_nil hne
        have hacc : accUnion l 1 = l.get ⟨0, h0⟩ := by
          have h0u : accUnion l 0 = (∅ : Set X) := by simp [accUnion_apply]
          rw [show (1 : ℕ) = 0 + 1 from rfl, accUnion_union, h0u, Set.empty_union]
          exact getD_eq_get_of_lt l h0
        rw [hacc]
        exact hsc _ (List.get_mem l ⟨0, h0⟩)
    | succ m ih =>
        intro hle
        have hm1 : m + 1 < l.length := by omega
        have hstep : SimplyConnectedSpace ↥(accUnion l (m + 1) ∪ l.getD (m + 1) ∅) :=
          simplyConnectedSpace_of_isOpen_union (hOpenAcc (m + 1)) (hOpenGetD (m + 1))
            (ih (by omega)) (hSCGetD (m + 1) hm1) (hPC m hm1)
        rw [accUnion_union l (m + 1)]
        exact hstep
  have hlen : 1 ≤ l.length := List.length_pos_of_ne_nil hne
  have hkey : SimplyConnectedSpace ↥(accUnion l l.length) := by
    have h := key (l.length - 1) (by omega)
    rwa [Nat.sub_add_cancel hlen] at h
  have hFinal : accUnion l l.length = ⋃ B ∈ l, (B : Set X) := by
    rw [accUnion_apply]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hx⟩
      rw [Finset.mem_range] at hi
      exact ⟨l.get ⟨i, hi⟩, List.get_mem l ⟨i, hi⟩,
        by rwa [← getD_eq_get_of_lt l hi]⟩
    · rintro ⟨B, hB, hx⟩
      obtain ⟨i, hi, hit⟩ := List.mem_iff_getElem.mp hB
      refine ⟨i, by rw [Finset.mem_range]; exact hi, ?_⟩
      rw [getD_eq_get_of_lt l hi, List.get_eq_getElem, hit]
      exact hx
  rw [← hFinal]
  exact hkey

end OmegaRangeMembership

end Work.SimplyConnected.ABS
