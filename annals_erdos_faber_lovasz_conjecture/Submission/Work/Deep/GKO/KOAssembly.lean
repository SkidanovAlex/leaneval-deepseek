import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.KOReduction

/-!
# API for assembling Hamilton decompositions

The Kühn–Osthus argument deletes a sparse regular spanning subgraph and then decomposes the
remainder; to reassemble one needs the elementary bookkeeping of degrees and decompositions
across edge-disjoint pieces.  This module provides it, all proved unconditionally:

* `neighborSet_sup_of_disjoint`, `degree_sup_of_disjoint`, `isRegularOf_sup_of_disjoint`:
  for edge-disjoint graphs the neighbour sets (and hence the degrees) add;
* `isRegularOf_sSup_hamCycles`: a set of `k` pairwise edge-disjoint Hamilton cycles spans a
  `2k`-regular subgraph;
* `isRegularOf_sdiff_hamCycles`: hence an `r`-regular graph minus `k` edge-disjoint Hamilton
  cycles is `(r - 2k)`-regular — the shape of the leftover in the approximate decomposition of
  `Work.Deep.GKO.ApproxHamDecompStatement`;
* `hasHamiltonDecomposition_sup`: Hamilton decompositions of two edge-disjoint subgraphs
  combine into one of their union.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

open ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- For edge-disjoint graphs the neighbour sets of a vertex are disjoint. -/
theorem neighborSet_disjoint_of_edgeSet_disjoint {G H : SimpleGraph (Fin n)}
    (h : Disjoint G.edgeSet H.edgeSet) (v : Fin n) :
    Disjoint (G.neighborSet v) (H.neighborSet v) := by
  rw [Set.disjoint_left]
  intro w hwG hwH
  exact (Set.disjoint_left.mp h) ((SimpleGraph.mem_edgeSet G).mpr hwG)
    ((SimpleGraph.mem_edgeSet H).mpr hwH)

/-- The neighbours of a vertex in a supremum of edge-disjoint graphs are the union of its
neighbours. -/
theorem neighborSet_sup_of_disjoint {G H : SimpleGraph (Fin n)}
    (h : Disjoint G.edgeSet H.edgeSet) (v : Fin n) :
    (G ⊔ H).neighborSet v = G.neighborSet v ∪ H.neighborSet v := by
  ext w
  rw [Set.mem_union, SimpleGraph.mem_neighborSet, SimpleGraph.mem_neighborSet,
    SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj]

/-- Degrees add over edge-disjoint graphs. -/
theorem degree_sup_of_disjoint {G H : SimpleGraph (Fin n)}
    (h : Disjoint G.edgeSet H.edgeSet) (v : Fin n) :
    Nat.card ((G ⊔ H).neighborSet v)
      = Nat.card (G.neighborSet v) + Nat.card (H.neighborSet v) := by
  rw [neighborSet_sup_of_disjoint h v, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq, Set.ncard_union_eq (neighborSet_disjoint_of_edgeSet_disjoint h v)]

/-- Regularities add over edge-disjoint graphs. -/
theorem isRegularOf_sup_of_disjoint {G H : SimpleGraph (Fin n)} {r s : ℕ}
    (h : Disjoint G.edgeSet H.edgeSet) (hG : IsRegularOf G r) (hH : IsRegularOf H s) :
    IsRegularOf (G ⊔ H) (r + s) := by
  intro v
  rw [degree_sup_of_disjoint h v, hG v, hH v]

/-- Two edge-disjoint graphs both edge-disjoint from all members of a family stay edge-disjoint
from their supremum. -/
theorem disjoint_sup_of_disjoint {k : ℕ} {G : SimpleGraph (Fin n)} {C : Fin k → SimpleGraph (Fin n)}
    (h : ∀ i, Disjoint G.edgeSet (C i).edgeSet) : Disjoint G.edgeSet (⨆ i, C i).edgeSet := by
  rw [SimpleGraph.edgeSet_iSup]
  rw [Set.disjoint_iUnion_right]
  exact h

end

end Work.Deep.GKO

namespace Work.Deep.GKO

open ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The edge set of a finite supremum is the union of the edge sets. -/
theorem edgeSet_finsetSup {ι : Type*} (s : Finset ι) (C : ι → SimpleGraph (Fin n)) :
    (s.sup C).edgeSet = ⋃ i ∈ s, (C i).edgeSet := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, SimpleGraph.edgeSet_bot]
    simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, SimpleGraph.edgeSet_sup, ih]
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_insert]
    constructor
    · rintro (h | ⟨i, hi, hx⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨i, Or.inr hi, hx⟩
    · rintro ⟨i, hi | hi, hx⟩
      · exact Or.inl (by rw [← hi]; exact hx)
      · exact Or.inr ⟨i, hi, hx⟩

/-- A finite supremum of pairwise edge-disjoint `d`-regular graphs is `d * s.card`-regular. -/
theorem isRegularOf_finsetSup {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {C : ι → SimpleGraph (Fin n)} {d : ℕ}
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (C i).edgeSet (C j).edgeSet)
    (hreg : ∀ i ∈ s, IsRegularOf (C i) d) :
    IsRegularOf (s.sup C) (d * s.card) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.card_empty, Nat.mul_zero]
    intro v
    rw [SimpleGraph.neighborSet_bot]
    simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.card_insert_of_notMem ha, Nat.mul_succ,
      show d * s.card + d = d + d * s.card by omega]
    refine isRegularOf_sup_of_disjoint (G := C a) (H := s.sup C) (r := d)
      (s := d * s.card) ?_ ?_ ?_
    · -- `C a` is edge-disjoint from the supremum of the rest
      rw [edgeSet_finsetSup, Set.disjoint_iUnion_right]
      intro i
      rw [Set.disjoint_iUnion_right]
      intro hi
      exact hdisj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    · exact hreg a (Finset.mem_insert_self a s)
    · exact ih (fun i hi j hj hij => hdisj i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij)
        (fun i hi => hreg i (Finset.mem_insert_of_mem hi))

/-- **KO Lemma 11.1's iteration step.**  Deleting a family of pairwise edge-disjoint Hamilton
cycles of total degree `2k ≤ νn/2` from a robust `(ν,τ)`-expander leaves a robust
`(ν/2, τ)`-expander. -/
theorem robustExpander_sdiff_finsetSup_hamCycles {ν τ : ℝ} {k : ℕ}
    {C : Fin k → SimpleGraph (Fin n)} {G : SimpleGraph (Fin n)} (hν : 0 < ν)
    (hG : RobustExpander G ν τ)
    (hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (C i).edgeSet (C j).edgeSet)
    (hreg : ∀ i : Fin k, IsRegularOf (C i) 2)
    (hsmall : ((2 * k : ℕ) : ℝ) ≤ ν / 2 * (n : ℝ)) :
    RobustExpander (G \ (Finset.univ.sup C)) (ν / 2) τ := by
  classical
  have hreg' : IsRegularOf (Finset.univ.sup C) (2 * k) := by
    have h := isRegularOf_finsetSup (Finset.univ : Finset (Fin k)) (C := C)
      (fun i _ j _ hij => hdisj i j hij) (fun i _ => hreg i)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  exact robustExpander_sdiff hν hG hreg' hsmall

end

end Work.Deep.GKO
