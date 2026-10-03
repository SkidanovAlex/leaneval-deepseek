/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The coedge basis of the `Z`-cover of a one-relator presentation

This file contains *definitions only* (no `sorry`), so that lemma requests may import it.

Let `c : α → ℤ` be a weight with `cohom c u = 1` (so that `u` is a closed walk in the `ℤ`-cover of
the rose at level `0`), and let `W : ℤ → FreeGroup α` be a gauge (`W 0 = 1`).  The decorated word
`decor c 0 (wordOf u)` is a walk on the levels `ℤ`; a decorated letter `p = ((x,i),b)` is a
*traversal* of the edge of the cover from level `i` to level `i + c x` labelled `x`, in the direction
given by `b`.

## Why the symbols must be *edges* and not *occurrences*

`coverRootDefs.coverBeta` indexes the generating set of the base by the *occurrences* of decorated
letters.  A closed walk revisits edges, and two occurrences of the same edge have the same loop class
(`coverClassAt`), so the class map on occurrences is not injective; moreover an edge traversed in both
directions contributes two occurrences whose loop classes are mutually inverse.  Both defects are
removed by indexing the symbols by *undirected edges of the cover*: the edge of a decorated letter
`p` is `p.1` (`coverEdge`), and the two traversals `((x,i),true)`, `((x,i),false)` of the same edge
share the key `(x,i)`, their loop classes being `coverClassAt W c (x,i)` and its inverse
(`coverClass_eq_coverClassAt_true/false`).  This is the generating set `coverBetaEdge`.

## The development map

`devAux W c u i L` reads the word `L` starting at level `i` and replaces each traversal by the symbol
of its edge (with the sign of the traversal) if that edge is in `coverBetaEdge W c u`, and by `1`
otherwise.  Two features make it a left inverse of the class map:

* `devAux` is invariant under the cancellation of an adjacent inverse pair, because such a pair
  traverses one edge in the two directions;
* for a *first-arrival* gauge (`uGauge`), the words `wordOf (W i)` traverse only edges of trivial
  loop class, hence only edges outside `coverBetaEdge`; consequently
  `devAux W c u 0 (edgeWord W c e) = of e` for `e` in `coverBetaEdge` (this is
  `devAux_edgeWord`), and expanding a reduced word in `FreeGroup (coverBetaEdge W c u)` and applying
  `devAux` returns it (`devAux_expand`).

Since `coedgeExpand` also represents the image of the class map (`mk_expand`), a word killed by the class
map is killed by `devAux 0`, hence is trivial: `coedgeToClasses_injective`.
-/
import Mathlib
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.gaugeLevelDefs
import Submission.Work.OROneRel.gauge_walk_defs
import Submission.Work.OROneRel.gauge_levels_bound
import Submission.Work.OROneRel.coverRootDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The walk of `u` and the first-arrival gauge -/

/-- The levels of the walk of `u` in the `ℤ`-cover: the running weights of the reduced word of `u`,
starting at level `0`. -/
noncomputable def walkLv (c : α → ℤ) (u : FreeGroup α) : List ℤ := lv c 0 (wordOf u)

/-- The labels of the walk of `u`: the letters of the reduced word of `u` as free-group elements. -/
noncomputable def walkLbl (u : FreeGroup α) : List (FreeGroup α) := lab (wordOf u)

/-- **The first-arrival gauge of the walk of `u`**: the level `i` carries the product of the labels
along the chain of levels by which the walk first reaches `i`.  Its discovering traversals have
literally trivial loop class (`walkGauge_triv`). -/
noncomputable def uGauge (c : α → ℤ) (u : FreeGroup α) : ℤ → FreeGroup α :=
  walkGauge (walkLv c u) (walkLbl u)

/-! ## The coedge generating set -/

/-- The *undirected edge* of the cover traversed by a decorated letter: the pair `(x,i)` meaning the
edge from level `i` to level `i + c x` labelled `x`.  The decorated letters `((x,i),true)` and
`((x,i),false)` are the two traversals of this edge. -/
def coverEdge (p : (α × ℤ) × Bool) : α × ℤ := p.1

/-- The loop class of the undirected edge `e = (x,i)` of the `ℤ`-cover under the gauge `W`:
`W i * x * (W (i + c x))⁻¹`.  It is the class of the traversal `((x,i),true)` and the inverse of the
class of `((x,i),false)`. -/
noncomputable def coverClassAt (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) : FreeGroup α :=
  gaugeMap W c (FreeGroup.of e)

/-- **The coedge generating set `β` of the `ℤ`-cover decomposition**: the edges of the cover that the
walk of `u` traverses and whose loop class is non-trivial.  Indexing by edges (rather than by
occurrences) is what makes the class map injective. -/
def coverBetaEdge (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) : Type u :=
  {e : α × ℤ // (∃ p ∈ decor c 0 (wordOf u), coverEdge p = e) ∧ coverClassAt W c e ≠ 1}

noncomputable instance coverBetaEdgeDecEq (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) :
    DecidableEq (coverBetaEdge W c u) := Classical.decEq _

/-- The class map `F (β) →* F α` of the coedge basis: a symbol is sent to the loop class of its edge. -/
noncomputable def coedgeToClasses (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) :
    FreeGroup (coverBetaEdge W c u) →* FreeGroup α :=
  FreeGroup.lift fun e => coverClassAt W c e.1

/-! ## The development map -/

/-- The symbol contributed by reading the letter `(a,b)` at running level `i`: the symbol of the edge
`(a,i)` (for `b = true`) or `(a,i - c a)` (for `b = false`), with the sign of the traversal, or `1`
if that edge is not in `β`. -/
noncomputable def devStep (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) (i : ℤ)
    (a : α) (b : Bool) : FreeGroup (coverBetaEdge W c u) := by
  classical
  exact
    if h : (∃ p ∈ decor c 0 (wordOf u), coverEdge p = (a, if b then i else i - c a)) ∧
        coverClassAt W c (a, if b then i else i - c a) ≠ 1 then
      (bif b then FreeGroup.of ⟨(a, if b then i else i - c a), h⟩
        else (FreeGroup.of ⟨(a, if b then i else i - c a), h⟩)⁻¹)
    else 1

/-- **The development of a word from a level.**  The word `L` is read starting at level `i`; every
traversal contributes the symbol of its edge (with the sign of the traversal), or `1` if the edge is
not in `β`. -/
noncomputable def devAux (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) :
    ℤ → List (α × Bool) → FreeGroup (coverBetaEdge W c u)
  | _, [] => 1
  | i, (a, true) :: L => devStep W c u i a true * devAux W c u (i + c a) L
  | i, (a, false) :: L => devStep W c u i a false * devAux W c u (i - c a) L

/-- The development of a word from level `0`. -/
noncomputable def dev (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α)
    (L : List (α × Bool)) : FreeGroup (coverBetaEdge W c u) :=
  devAux W c u 0 L

/-! ## The expansion of a word in the coedge basis -/

/-- The word of the loop of the edge `e = (x,i)` based at level `0`:
`wordOf (W i) ++ [(x,true)] ++ wordOf ((W (i + c x))⁻¹)`.  Read from level `0` it traverses the tree
path from `0` to `i`, then the edge, then the tree path back, so its development is the symbol of
`e`.  Its image in `F α` is the loop class of `e`. -/
noncomputable def edgeWord (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) : List (α × Bool) :=
  wordOf (W e.2) ++ [(e.1, true)] ++ wordOf ((W (e.2 + c e.1))⁻¹)

/-- The word of the loop of the edge `e` traversed in the direction `b` (`b = false` gives the
inverse word). -/
noncomputable def edgeWordSigned (W : ℤ → FreeGroup α) (c : α → ℤ) (e : α × ℤ) (b : Bool) :
    List (α × Bool) :=
  bif b then edgeWord W c e else FreeGroup.invRev (edgeWord W c e)

/-- **The expansion of a word in the coedge basis**: the word in `(α × Bool)` obtained by replacing
each symbol `e^±` by the loop word of the corresponding traversal of `e`.  Its image in `F α` is the
image of the word under the class map, and its development is the word itself. -/
noncomputable def coedgeExpand (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α)
    (w : FreeGroup (coverBetaEdge W c u)) : List (α × Bool) :=
  ((FreeGroup.toWord w).map (fun p => edgeWordSigned W c p.1.1 p.2)).flatten

/-! ## The candidate root, indexed by coedges -/

/-- The traversals of the walk of `u` whose edge lies in the coedge basis `β`, as a word over `β`
(the exponent records the direction of the traversal). -/
noncomputable def coedgeRootList (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) :
    List (coverBetaEdge W c u × Bool) := by
  classical
  exact (decor c 0 (wordOf u)).attach.filterMap
    (fun q : {p // p ∈ decor c 0 (wordOf u)} =>
      if h : (∃ p ∈ decor c 0 (wordOf u), coverEdge p = coverEdge q.1) ∧
          coverClassAt W c (coverEdge q.1) ≠ 1 then
        some (⟨coverEdge q.1, h⟩, q.1.2)
      else none)

/-- **The candidate root of the `Z`-cover decomposition, indexed by coedges**: the word spelled by the
traversals of the walk of `u` whose edge lies in `β`. -/
noncomputable def coedgeRoot (W : ℤ → FreeGroup α) (c : α → ℤ) (u : FreeGroup α) :
    FreeGroup (coverBetaEdge W c u) :=
  FreeGroup.mk (coedgeRootList W c u)

/-- **The loop class of a decorated letter is the signed loop class of its edge.** -/
theorem coverClass_eq_signed_coverClassAt (W : ℤ → FreeGroup α) (c : α → ℤ)
    (p : (α × ℤ) × Bool) :
    coverClass W c p = bif p.2 then coverClassAt W c (coverEdge p)
      else (coverClassAt W c (coverEdge p))⁻¹ := by
  obtain ⟨⟨a, i⟩, b⟩ := p
  cases b <;> simp [coverClass, coverClassAt, coverEdge]

end Work.OROneRel
