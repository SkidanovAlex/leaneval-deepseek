/-
# The naive colouring procedure: the model

This module sets up the random experiment of the naive colouring procedure
(Molloy–Reed, *Graph Colouring and the Probabilistic Method*, Chapter 10; Bruhn–Joos;
Bonamy–Perrett–Postle, arXiv:1810.06704, §3) on top of the probability layer
`Submission.Work.Deep.Sparse.ProbBasic`.

* `Retained G f v` — under the colouring `f : V → Fin k`, the vertex `v` has no neighbour of
  the same colour (so it *keeps* its colour).
* `ofColoring G f` — the partial proper colouring in which exactly the retained vertices keep
  their colour: the outcome of the naive colouring procedure on `G` with `k` colours.
* `nonAdjPairs G v` — the ordered pairs of distinct non-adjacent neighbours of `v`; the
  sparsity hypothesis of `SparseGraphStatement` lower-bounds its cardinality.
* `indepTriples G v` — the independent 3-element subsets of `N(v)`; these are the only triples
  of neighbours that can ever carry one colour of the partial colouring.
* `collisionPairs G f v`, `collisionTriples G f v` — the ordered pairs/triples of distinct
  retained neighbours of `v` that carry the same colour under `f`.

The two counting identities relating `collisionPairs`/`collisionTriples` to the partial
colouring's `pairTerm`/`tripleTerm`, the expectation bounds for `pairTerm`/`tripleTerm`, the
triangle count for `indepTriples`, the concentration of `pairTerm - tripleTerm`, and the
assembly into `NCPCore` are stated in the sibling modules of this directory.
-/
import Submission.Work.Deep.Sparse.Basic
import Submission.Work.Deep.Sparse.ProbBasic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Sparse

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Under the colouring `f`, the vertex `v` **retains** its colour: no neighbour of `v` has the
same colour as `v`. -/
abbrev Retained (G : SimpleGraph V) {k : ℕ} (f : V → Fin k) (v : V) : Prop :=
  ∀ w : V, G.Adj v w → f w ≠ f v

/-- The partial proper colouring produced by the naive colouring procedure: a vertex keeps its
colour exactly when it retains it. -/
noncomputable def ofColoring (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (f : V → Fin k) : PartialColoring G k := by
  classical
  exact
  { col := fun v => if Retained G f v then some (f v) else none
    isProper := by
      intro u v huv hEq
      by_cases hu : Retained G f u
      · rw [if_pos hu] at hEq
        by_cases hv : Retained G f v
        · rw [if_pos hv] at hEq
          exact absurd (Option.some.inj hEq).symm (hu v huv)
        · rw [if_neg hv] at hEq
          exact absurd hEq (by simp)
      · rw [if_neg hu] }

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The ordered pairs of distinct, non-adjacent neighbours of `v`. -/
def nonAdjPairs (v : V) : Finset (V × V) :=
  ((G.neighborFinset v).product (G.neighborFinset v)).filter
    (fun p => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2)

/-- The independent 3-element subsets of `N(v)`. -/
def indepTriples (v : V) : Finset (Finset V) :=
  ((G.neighborFinset v).powersetCard 3).filter
    (fun s => ∀ x ∈ s, ∀ y ∈ s, G.Adj x y → x = y)

/-- The ordered pairs of distinct retained neighbours of `v` that carry the same colour. -/
noncomputable def collisionPairs {k : ℕ} (f : V → Fin k) (v : V) : Finset (V × V) :=
  ((G.neighborFinset v).product (G.neighborFinset v)).filter
    (fun p => p.1 ≠ p.2 ∧ Retained G f p.1 ∧ Retained G f p.2 ∧ f p.1 = f p.2)

/-- The ordered triples of distinct retained neighbours of `v` that carry the same colour. -/
noncomputable def collisionTriples {k : ℕ} (f : V → Fin k) (v : V) : Finset (V × V × V) :=
  (((G.neighborFinset v).product ((G.neighborFinset v).product (G.neighborFinset v))).filter
    (fun q => q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2 ∧
      Retained G f q.1 ∧ Retained G f q.2.1 ∧ Retained G f q.2.2 ∧
      f q.1 = f q.2.1 ∧ f q.2.1 = f q.2.2))

@[simp] lemma mem_nonAdjPairs {v : V} {p : V × V} :
    p ∈ nonAdjPairs G v ↔ p.1 ∈ G.neighborFinset v ∧ p.2 ∈ G.neighborFinset v ∧
      p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2 := by
  simp [nonAdjPairs, Finset.mem_product, and_assoc]

@[simp] lemma mem_indepTriples {v : V} {s : Finset V} :
    s ∈ indepTriples G v ↔ s ⊆ G.neighborFinset v ∧ s.card = 3 ∧
      (∀ x ∈ s, ∀ y ∈ s, G.Adj x y → x = y) := by
  simp [indepTriples, Finset.mem_powersetCard, and_assoc]

@[simp] lemma mem_collisionPairs {k : ℕ} {f : V → Fin k} {v : V} {p : V × V} :
    p ∈ collisionPairs G f v ↔ p.1 ∈ G.neighborFinset v ∧ p.2 ∈ G.neighborFinset v ∧
      p.1 ≠ p.2 ∧ Retained G f p.1 ∧ Retained G f p.2 ∧ f p.1 = f p.2 := by
  simp [collisionPairs, Finset.mem_product, and_assoc, and_left_comm, and_comm]

@[simp] lemma mem_collisionTriples {k : ℕ} {f : V → Fin k} {v : V} {q : V × V × V} :
    q ∈ collisionTriples G f v ↔
      q.1 ∈ G.neighborFinset v ∧ q.2.1 ∈ G.neighborFinset v ∧ q.2.2 ∈ G.neighborFinset v ∧
      q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2 ∧ q.2.1 ≠ q.2.2 ∧
      Retained G f q.1 ∧ Retained G f q.2.1 ∧ Retained G f q.2.2 ∧
      f q.1 = f q.2.1 ∧ f q.2.1 = f q.2.2 := by
  simp [collisionTriples, Finset.mem_product, and_assoc, and_left_comm, and_comm]

/-- The number of coloured neighbours of `v` of colour `c`, written in terms of the colouring
`f` rather than the partial colouring. -/
noncomputable def colourClassCount {k : ℕ} (f : V → Fin k) (v : V) (c : Fin k) : ℕ :=
  ((G.neighborFinset v).filter (fun x => Retained G f x ∧ f x = c)).card

@[simp] lemma colourClassCount_eq {k : ℕ} (f : V → Fin k) (v : V) (c : Fin k) :
    colourClassCount G f v c
      = ((G.neighborFinset v).filter (fun x => Retained G f x ∧ f x = c)).card := rfl

/-- The colours occurring on retained neighbours of `v` are exactly the colour classes of `v`. -/
lemma pairTerm_ofColoring {k : ℕ} (f : V → Fin k) (v : V) :
    (ofColoring G f).pairTerm v = ∑ c, (colourClassCount G f v c).choose 2 := by
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [PartialColoring.colCount, colourClassCount]
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro x _
  by_cases hx : Retained G f x
  · simp [ofColoring, hx]
  · simp [ofColoring, hx]

/-- The triples version of `pairTerm_ofColoring`. -/
lemma tripleTerm_ofColoring {k : ℕ} (f : V → Fin k) (v : V) :
    (ofColoring G f).tripleTerm v = ∑ c, (colourClassCount G f v c).choose 3 := by
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [PartialColoring.colCount, colourClassCount]
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro x _
  by_cases hx : Retained G f x
  · simp [ofColoring, hx]
  · simp [ofColoring, hx]

end Work.Deep.Sparse
