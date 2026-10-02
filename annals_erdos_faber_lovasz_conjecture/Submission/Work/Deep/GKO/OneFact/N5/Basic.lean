import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Defs
import Submission.Work.Deep.GKO.OneFactDefs
import Submission.Work.Deep.GKO.RegVocab

/-!
# The counting vocabulary of the N5 iteration (`EFL_N5_LEAD.md` §2, §3)

This module holds the definitions and the elementary lemmas that the three N5 nodes
(`insideNearPerfectClasses` N5a, `completeInsideMatching` N5b, `completeAllClasses` N5c) share.

The point of the N5 stage is to *complete* each matching `N j` of a family of pairwise
edge-disjoint inside matchings to a perfect matching `P j` of `N j ⊔ K₀`, while using each cross
edge at most once over the whole family and re-matching each vertex at most `L` times.  The
counting vocabulary is therefore:

* `uncov M` (in `Defs.lean`): the vertices not covered by `M`;
* `Rematched N P v` (in `Defs.lean`): `P` uses at `v` an edge that `N` does not;
* `cntOf N P v`: the number of classes `j` that re-match `v`;
* `missOf N v`: the number of classes that leave `v` uncovered;
* `usedEdges P`: the set of edges occurring in one of the `P j`;
* `remaining K P := K.deleteEdges (usedEdges P)`: the cross edges of `K` not yet consumed;
* `usedNbrs K P v`: the neighbours `w` of `v` in `K` joined to `v` by an edge already used by
  one of the `P j` — the neighbours that `remaining K P` has lost at `v`.

The two "sides" `A` and `B` of the bipartition are packaged as `IsCrossPair A B u v` (the edge
`uv` is a `K₀`-edge) and `IsInsidePair A B u v` (the edge `uv` is an `N j`-edge); the lemmas
`cross_or_inside` and `not_inside_of_cross` are the only facts about the partition that the
later arguments use.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators
open Classical

namespace Work.Deep.GKO.OneFact.N5

noncomputable section

variable {n c : ℕ}

/-! ## The two sides of the bipartition -/

/-- `uv` **is a cross pair**: one end in `A`, the other in `B`. -/
def IsCrossPair (A B : Finset (Fin n)) (u v : Fin n) : Prop :=
  (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)

/-- `uv` **is an inside pair**: both ends in the same side. -/
def IsInsidePair (A B : Finset (Fin n)) (u v : Fin n) : Prop :=
  (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)

theorem disjoint_pairA {A B : Finset (Fin n)} (hAB : Disjoint A B) {x : Fin n}
    (h : x ∈ A) : x ∉ B := Finset.disjoint_left.mp hAB h

theorem disjoint_pairB {A B : Finset (Fin n)} (hAB : Disjoint A B) {x : Fin n}
    (h : x ∈ B) : x ∉ A := Finset.disjoint_right.mp hAB h

/-- A cross pair is never an inside pair. -/
theorem not_inside_of_cross {A B : Finset (Fin n)} (hAB : Disjoint A B) {u v : Fin n}
    (hc : IsCrossPair A B u v) : ¬ IsInsidePair A B u v := by
  rcases hc with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> intro hi
  · rcases hi with ⟨hu2, hv2⟩ | ⟨hu2, hv2⟩
    · exact disjoint_pairA hAB hv2 hv
    · exact disjoint_pairA hAB hu hu2
  · rcases hi with ⟨hu2, hv2⟩ | ⟨hu2, hv2⟩
    · exact disjoint_pairB hAB hu hu2
    · exact disjoint_pairB hAB hv2 hv

/-- An inside pair is never a cross pair. -/
theorem not_cross_of_inside {A B : Finset (Fin n)} (hAB : Disjoint A B) {u v : Fin n}
    (hi : IsInsidePair A B u v) : ¬ IsCrossPair A B u v := by
  intro hc
  exact not_inside_of_cross hAB hc hi

/-- Every pair of vertices of the covering pair `(A,B)` is either cross or inside. -/
theorem cross_or_inside {A B : Finset (Fin n)} (hcov : A ∪ B = Finset.univ) {u v : Fin n} :
    IsCrossPair A B u v ∨ IsInsidePair A B u v := by
  have hu : u ∈ A ∨ u ∈ B := by
    have h : u ∈ A ∪ B := by rw [hcov]; exact Finset.mem_univ u
    exact Finset.mem_union.mp h
  have hv : v ∈ A ∨ v ∈ B := by
    have h : v ∈ A ∪ B := by rw [hcov]; exact Finset.mem_univ v
    exact Finset.mem_union.mp h
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact Or.inr (Or.inl ⟨hu, hv⟩)
  · exact Or.inl (Or.inl ⟨hu, hv⟩)
  · exact Or.inl (Or.inr ⟨hu, hv⟩)
  · exact Or.inr (Or.inr ⟨hu, hv⟩)

/-! ## The counting vocabulary -/

/-- The number of classes `j` on which `P j` re-matches the vertex `v` (a covered vertex of
`N j` is re-matched when `P j` uses at `v` an edge that `N j` does not). -/
def cntOf (N P : Fin c → SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun j => v ∉ uncov (N j) ∧ Rematched (N j) (P j) v).card

/-- The number of classes `j` on which `v` is left uncovered by `N j`. -/
def missOf (N : Fin c → SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun j => v ∈ uncov (N j)).card

/-- The set of edges used by the family `P`. -/
def usedEdges (P : Fin c → SimpleGraph (Fin n)) : Set (Sym2 (Fin n)) :=
  ⋃ i, (P i).edgeSet

/-- The edges of `K` that are not used by any member of `P`. -/
def remaining (K : SimpleGraph (Fin n)) (P : Fin c → SimpleGraph (Fin n)) :
    SimpleGraph (Fin n) :=
  K.deleteEdges (usedEdges P)

/-- The neighbours `w` of `v` in `K` such that the edge `vw` is used by one of the `P i`. -/
def usedNbrs (K : SimpleGraph (Fin n)) (P : Fin c → SimpleGraph (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun w => K.Adj v w ∧ ∃ i : Fin c, (P i).Adj v w

/-- The `K`-neighbours of `v` used by the single class `Pl`. -/
def useCount (K Pl : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun w => K.Adj v w ∧ Pl.Adj v w).card

/-- The per-vertex budget that a single class `Pl` consumes: `1` if `N` misses `v`, plus `1` if
`Pl` re-matches `v`.  (This is the indicator pair into which `missOf` and `cntOf` split when the
family is extended by one class; it is a `def` so that statements about it need no decidability
instances.) -/
def crossUseInd (N Pl : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  (if v ∈ uncov N then 1 else 0) + (if v ∉ uncov N ∧ Rematched N Pl v then 1 else 0)

/-- The indicator of "`N` misses `v`", packaged as a `def` so that statements about it carry no
decidability instances. -/
def missInd (N : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  if v ∈ uncov N then 1 else 0

/-- The indicator of "`Pl` re-matches the covered vertex `v` of `N`", packaged as a `def` so that
statements about it carry no decidability instances. -/
def rematchInd (N Pl : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  if v ∉ uncov N ∧ Rematched N Pl v then 1 else 0

theorem crossUseInd_eq (N Pl : SimpleGraph (Fin n)) (v : Fin n) :
    crossUseInd N Pl v = missInd N v + rematchInd N Pl v :=
  rfl

theorem missInd_le_one (N : SimpleGraph (Fin n)) (v : Fin n) : missInd N v ≤ 1 := by
  rw [missInd]; split <;> omega

theorem rematchInd_le_one (N Pl : SimpleGraph (Fin n)) (v : Fin n) : rematchInd N Pl v ≤ 1 := by
  rw [rematchInd]; split <;> omega

theorem missInd_eq_one {N : SimpleGraph (Fin n)} {v : Fin n} (h : v ∈ uncov N) :
    missInd N v = 1 := by
  rw [missInd, if_pos h]

theorem missInd_eq_zero {N : SimpleGraph (Fin n)} {v : Fin n} (h : v ∉ uncov N) :
    missInd N v = 0 := by
  rw [missInd, if_neg h]

theorem rematchInd_eq_one {N Pl : SimpleGraph (Fin n)} {v : Fin n}
    (h : v ∉ uncov N ∧ Rematched N Pl v) : rematchInd N Pl v = 1 := by
  rw [rematchInd, if_pos h]

theorem rematchInd_eq_zero {N Pl : SimpleGraph (Fin n)} {v : Fin n}
    (h : ¬ (v ∉ uncov N ∧ Rematched N Pl v)) : rematchInd N Pl v = 0 := by
  rw [rematchInd, if_neg h]

/-- The total re-match count of one class equals the size of its re-matched set. -/
theorem sum_rematchInd_eq_ncard (Nl Pl : SimpleGraph (Fin n)) :
    (∑ v, rematchInd Nl Pl v)
      = ({v : Fin n | v ∉ uncov Nl ∧ Rematched Nl Pl v} : Set (Fin n)).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  have htof : ({v : Fin n | v ∉ uncov Nl ∧ Rematched Nl Pl v} : Set (Fin n)).toFinset
      = Finset.univ.filter (fun v => rematchInd Nl Pl v = 1) := by
    ext v
    rw [Set.mem_toFinset]
    constructor
    · intro h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, rematchInd_eq_one h⟩
    · intro h
      by_contra hc
      have h1 : rematchInd Nl Pl v = 1 := (Finset.mem_filter.mp h).2
      rw [rematchInd_eq_zero hc] at h1
      exact one_ne_zero h1.symm
  rw [htof, Finset.card_filter]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases hh : rematchInd Nl Pl v = 1
  · simp [hh]
  · have h0 : rematchInd Nl Pl v = 0 := by
      have := rematchInd_le_one Nl Pl v; omega
    simp [hh, h0]

/-! ## Elementary API -/

@[simp] theorem mem_uncov (M : SimpleGraph (Fin n)) (v : Fin n) :
    v ∈ uncov M ↔ ∀ w, ¬ M.Adj v w := by
  simp [uncov]

theorem not_mem_uncov (M : SimpleGraph (Fin n)) (v : Fin n) :
    v ∉ uncov M ↔ ∃ w, M.Adj v w := by
  rw [mem_uncov]
  push Not
  rfl

@[simp] theorem mem_usedNbrs {K : SimpleGraph (Fin n)} {P : Fin c → SimpleGraph (Fin n)}
    {v w : Fin n} : w ∈ usedNbrs K P v ↔ K.Adj v w ∧ ∃ i : Fin c, (P i).Adj v w := by
  simp [usedNbrs]

theorem usedNbrs_subset_neighborSet (K : SimpleGraph (Fin n)) (P : Fin c → SimpleGraph (Fin n))
    (v : Fin n) : ↑(usedNbrs K P v) ⊆ K.neighborSet v := by
  intro w hw
  rw [Finset.mem_coe, mem_usedNbrs] at hw
  exact hw.1

@[simp] theorem remaining_adj (K : SimpleGraph (Fin n)) (P : Fin c → SimpleGraph (Fin n))
    (v w : Fin n) :
    (remaining K P).Adj v w ↔ K.Adj v w ∧ s(v, w) ∉ usedEdges P :=
  SimpleGraph.deleteEdges_adj

theorem remaining_le (K : SimpleGraph (Fin n)) (P : Fin c → SimpleGraph (Fin n)) :
    remaining K P ≤ K := SimpleGraph.deleteEdges_le _

theorem mem_usedEdges {P : Fin c → SimpleGraph (Fin n)} {u v : Fin n} :
    s(u, v) ∈ usedEdges P ↔ ∃ i : Fin c, (P i).Adj u v := by
  simp [usedEdges, SimpleGraph.mem_edgeSet]

theorem mem_usedEdges' {P : Fin c → SimpleGraph (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ usedEdges P ↔ ∃ i : Fin c, e ∈ (P i).edgeSet := by
  simp [usedEdges]

theorem usedEdges_mono {P Q : Fin c → SimpleGraph (Fin n)}
    (h : ∀ i, P i ≤ Q i) : usedEdges P ⊆ usedEdges Q := by
  intro e he
  rw [mem_usedEdges'] at he ⊢
  obtain ⟨i, hi⟩ := he
  exact ⟨i, SimpleGraph.edgeSet_mono (h i) hi⟩

/-- Disjointness of edge sets, restated with adjacency (avoids `Sym2` bookkeeping). -/
theorem disjoint_edgeSet_iff {G H : SimpleGraph (Fin n)} :
    Disjoint G.edgeSet H.edgeSet ↔ ∀ u v, G.Adj u v → ¬ H.Adj u v := by
  rw [Set.disjoint_left]
  constructor
  · intro h u v huv h2
    exact h (by rwa [SimpleGraph.mem_edgeSet]) (by rwa [SimpleGraph.mem_edgeSet])
  · intro h e he1 he2
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he1 he2
      exact h u v he1 he2

/-! ## Splitting a family indexed by `Fin (c+1)` into its first `c` members and the last one -/

theorem cntOf_snoc (N : Fin c → SimpleGraph (Fin n)) (Nl : SimpleGraph (Fin n))
    (P : Fin c → SimpleGraph (Fin n)) (Pl : SimpleGraph (Fin n)) (v : Fin n) :
    cntOf (Fin.snoc N Nl) (Fin.snoc P Pl) v
      = cntOf N P v + (if v ∉ uncov Nl ∧ Rematched Nl Pl v then 1 else 0) := by
  rw [cntOf, cntOf, Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem missOf_snoc (N : Fin c → SimpleGraph (Fin n)) (Nl : SimpleGraph (Fin n)) (v : Fin n) :
    missOf (Fin.snoc N Nl) v = missOf N v + (if v ∈ uncov Nl then 1 else 0) := by
  rw [missOf, missOf, Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem card_filter_fin_succ_le (φ : Fin (c + 1) → Prop) (ψ : Fin c → Prop)
    (h : ∀ j : Fin c, φ j.castSucc → ψ j) :
    (Finset.univ.filter φ).card ≤ (Finset.univ.filter ψ).card + (if φ (Fin.last c) then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  refine Nat.add_le_add ?_ le_rfl
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hφ : φ j.castSucc <;> by_cases hψ : ψ j <;> simp_all

/-- The two per-class counts of a family extended by one class, split off the last class. -/
theorem missOf_add_cntOf_snoc (N : Fin c → SimpleGraph (Fin n)) (Nl : SimpleGraph (Fin n))
    (P : Fin c → SimpleGraph (Fin n)) (Pl : SimpleGraph (Fin n)) (v : Fin n) :
    missOf (Fin.snoc N Nl) v + cntOf (Fin.snoc N Nl) (Fin.snoc P Pl) v
      = missOf N v + cntOf N P v + crossUseInd Nl Pl v := by
  rw [missOf_snoc, cntOf_snoc, crossUseInd]
  omega

/-- `missOf` of a family extended by one class, with the indicator packaged as a `def`. -/
theorem missOf_snoc_ind (N : Fin c → SimpleGraph (Fin n)) (Nl : SimpleGraph (Fin n))
    (v : Fin n) :
    missOf (Fin.snoc N Nl) v = missOf N v + missInd Nl v := by
  rw [missOf_snoc, missInd]

/-- `cntOf` of a family extended by one class, with the indicator packaged as a `def`. -/
theorem cntOf_snoc_ind (N : Fin c → SimpleGraph (Fin n)) (Nl : SimpleGraph (Fin n))
    (P : Fin c → SimpleGraph (Fin n)) (Pl : SimpleGraph (Fin n)) (v : Fin n) :
    cntOf (Fin.snoc N Nl) (Fin.snoc P Pl) v = cntOf N P v + rematchInd Nl Pl v := by
  rw [cntOf_snoc, rematchInd]

/-- The register-4 identity of the iteration, with the indicators packaged as `def`s. -/
theorem missOf_add_cntOf_snoc_ind (N : Fin c → SimpleGraph (Fin n)) (Nl : SimpleGraph (Fin n))
    (P : Fin c → SimpleGraph (Fin n)) (Pl : SimpleGraph (Fin n)) (v : Fin n) :
    missOf (Fin.snoc N Nl) v + cntOf (Fin.snoc N Nl) (Fin.snoc P Pl) v
      = missOf N v + cntOf N P v + crossUseInd Nl Pl v :=
  missOf_add_cntOf_snoc N Nl P Pl v

/-- Extending a family by one class increases `cntOf` by at most one at every vertex. -/
theorem cntOf_snoc_le (N : Fin c → SimpleGraph (Fin n)) (Nl : SimpleGraph (Fin n))
    (P : Fin c → SimpleGraph (Fin n)) (Pl : SimpleGraph (Fin n)) (v : Fin n) :
    cntOf (Fin.snoc N Nl) (Fin.snoc P Pl) v ≤ cntOf N P v + 1 := by
  rw [cntOf_snoc_ind]
  have := rematchInd_le_one Nl Pl v
  omega

/-- A perfect matching is a matching. -/
theorem IsPerfectMatching'.isMatching' {G M : SimpleGraph (Fin n)}
    (h : IsPerfectMatching' G M) : IsMatching' M := by
  intro v w w' hw hw'
  obtain ⟨u, hu, huniq⟩ := h.2 v
  have h1 : w = u := huniq w hw
  have h2 : w' = u := huniq w' hw'
  rw [h1, h2]

/-- The `Set.ncard` form of `cntOf`, which is the form in which the conclusion of N5b is
stated. -/
theorem ncard_cntOf (N P : Fin c → SimpleGraph (Fin n)) (v : Fin n) :
    ({j : Fin c | v ∉ uncov (N j) ∧ Rematched (N j) (P j) v} : Set (Fin c)).ncard
      = cntOf N P v := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext j
  simp

/-! ## Restriction to the first `c` classes -/

theorem missOf_castSucc_le (N : Fin (c + 1) → SimpleGraph (Fin n)) (v : Fin n) :
    missOf (fun j : Fin c => N j.castSucc) v ≤ missOf N v := by
  rw [missOf, missOf, Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  exact Nat.le_add_right _ _

theorem snoc_castSucc_last (N : Fin (c + 1) → SimpleGraph (Fin n)) :
    Fin.snoc (fun j : Fin c => N j.castSucc) (N (Fin.last c)) = N := by
  funext j
  exact Fin.lastCases (by simp) (fun _ => by simp) j

/-- The neighbours lost by `remaining K P` at `v` are among `usedNbrs K P v`. -/
theorem remaining_neighborSet_subset (K : SimpleGraph (Fin n))
    (P : Fin c → SimpleGraph (Fin n)) (v : Fin n) :
    (remaining K P).neighborSet v ⊆ K.neighborSet v \ (usedNbrs K P v : Set (Fin n)) := by
  intro w hw
  rw [SimpleGraph.mem_neighborSet] at hw
  rw [remaining_adj] at hw
  refine ⟨by rw [SimpleGraph.mem_neighborSet]; exact hw.1, ?_⟩
  intro hmem
  rw [Finset.mem_coe, mem_usedNbrs] at hmem
  obtain ⟨i, hi⟩ := hmem.2
  exact hw.2 (by rw [mem_usedEdges]; exact ⟨i, hi⟩)

/-! ## Snoc bookkeeping for the two counts and for `usedNbrs` -/

theorem usedNbrs_snoc_subset (K : SimpleGraph (Fin n))
    (P : Fin c → SimpleGraph (Fin n)) (Pl : SimpleGraph (Fin n)) (v : Fin n) :
    usedNbrs K (Fin.snoc P Pl) v ⊆
      usedNbrs K P v ∪ (Finset.univ.filter fun w => K.Adj v w ∧ Pl.Adj v w) := by
  intro w hw
  rw [mem_usedNbrs] at hw
  obtain ⟨hKw, i, hi⟩ := hw
  rw [Finset.mem_union]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · left
    rw [mem_usedNbrs]
    exact ⟨hKw, j, by simpa using hi⟩
  · right
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hKw, by simpa using hi⟩


/-- The number of used `K`-neighbours grows by at most the number of `K`-neighbours used by the
last class when the family is extended by one class. -/
theorem usedNbrs_snoc_card_le (K : SimpleGraph (Fin n))
    (P : Fin c → SimpleGraph (Fin n)) (Pl : SimpleGraph (Fin n)) (v : Fin n) :
    (usedNbrs K (Fin.snoc P Pl) v).card ≤ (usedNbrs K P v).card + useCount K Pl v := by
  calc (usedNbrs K (Fin.snoc P Pl) v).card
      ≤ (usedNbrs K P v ∪ (Finset.univ.filter fun w => K.Adj v w ∧ Pl.Adj v w)).card :=
        Finset.card_le_card (usedNbrs_snoc_subset K P Pl v)
    _ ≤ (usedNbrs K P v).card
          + (Finset.univ.filter fun w => K.Adj v w ∧ Pl.Adj v w).card := Finset.card_union_le _ _
    _ = (usedNbrs K P v).card + useCount K Pl v := rfl

end

end Work.Deep.GKO.OneFact.N5
