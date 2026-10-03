import Mathlib
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.coverCoedgeDefs

/-!
# The window basis of the `Z`-cover decomposition

This file fixes the *correct* alphabet for the vertex of the `Z`-domain decomposition of
`⟨α | u ^ l⟩`, namely the **non-tree edges of a window** `E(D) ∖ T` of the level graph, with the
**tree-path gauge**; see `Submission/Work/OROneRel/NOTES_magnusStepCase2_crux.md`, Facts 4--5: the
Freiheitssatz obligation `ρ ⁻¹' ⟪u^l⟫ = ⟪v^l⟫` is *false* for the occurrence-indexed basis
`coverBeta` (`coverRootDefs.lean`) and for the traversed-edge basis `coverBetaEdge`
(`coverCoedgeDefs.lean`) at a general gauge.

## The level graph and the window

The `Z`-cover `Y` of the one-relator complex `⟨α | u^l⟩` has vertices the levels `ℤ` and, for every
generator `x : α`, one edge `(x,i) : i → i + c x`.  A **window** `[lo,hi]` is a set of levels; the
**edges of the window** `winE c lo hi` are those both of whose endpoints lie in `[lo,hi]`.  A
**gauge** is a family `Wt : ℤ → FreeGroup α` with `cohom c (Wt i) = ofAdd i` (so each `Wt i` is a
word of level `i`) and `Wt 0 = 1`; the **loop class** of the edge `e = (x,i)` is
`coverClassAt Wt c e = Wt i · x · (Wt (i + c x))⁻¹`.  For the **tree-path gauge** of a spanning tree
`T` of the window (`Wt i` = the word of the tree path from level `0` to level `i`) the edges of
trivial loop class are exactly the edges of `T`.

## Contents

* `winE c lo hi` -- the edge set `E(D)` of the window;
* `winTree Wt c lo hi` -- the edges of trivial loop class (the tree);
* `winBeta Wt c lo hi` -- the complement `β = E(D) ∖ T`, the alphabet of the vertex;
* `winRho Wt c lo hi` -- the class map `F (β) →* F α`, `e ↦ coverClassAt Wt c e`;
* `winRootList` / `winRoot` -- the deleted walk word `v ∈ F (β)`: the traversals of the walk of `u`
  whose edge lies in the window and has non-trivial loop class.  The word is *edge-indexed*: the
  generator attached to a traversal is its edge, so the two traversals of one edge give the same
  generator, carrying the sign of the traversal;
* `winRho_cond_class` -- the sign convention, relating the `β`-word of a traversal to the loop class
  of the traversal.

## What is *not* here

The obligations of the residual of `Work.OROneRel.magnusStepCase2` in this vocabulary are delegated
separately (each in its own file, importing this one):

* `Work.OROneRel.winRho_winRoot` -- the telescoping identity `winRho (winRoot) = u` (which follows
  from `gauge_truncation`) and hence the *easy* half of the Freiheitssatz,
  `x ∈ ⟪v^l⟫ → winRho x ∈ ⟪u^l⟫`;
* `Work.OROneRel.winFreiheitssatz` -- the Freiheitssatz of the domain, i.e. the other half
  `winRho x ∈ ⟪u^l⟫ → x ∈ ⟪v^l⟫` (Linton, *One-relator hierarchies*, arXiv 2202.11324, §4);
* `Work.OROneRel.winRootNormLt` -- `relatorNorm v < relatorNorm u`;
* `Work.OROneRel.winVertexSplits` -- Britton for `(H, t)` in `G = ⟨α | u^l⟩` with `H` the image of
  the vertex, i.e. the graph-of-spaces splitting over the line of window domains.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The edges of the window `[lo,hi]`** of the level graph: the edges `(x,i)` *both* of whose
endpoints `i` and `i + c x` lie in `[lo,hi]`.

**All four conditions are needed** (a fact discovered by refutation, see
`Submission/Work/OROneRel/NOTES_magnusStepCase2_crux.md`): bounding only the base from below and the
target from above (`lo ≤ e.2 ∧ e.2 + c e.1 ≤ hi`) would place the edge `(x,i)` in the window for
`i > hi` whenever `c x < 0`, and the loop class of such an edge is then unconstrained by any
tree-path gauge (which only sees the levels in `[lo,hi]`), so it could be made equal to `u` and the
Freiheitssatz would fail.  With all four conditions, "the walk of `w` lies in the window" is exactly
the four-conjunct statement produced by `Work.OROneRel.band_one_lift`. -/
def winE (c : α → ℤ) (lo hi : ℤ) : Set (α × ℤ) :=
  {e | lo ≤ e.2 ∧ e.2 ≤ hi ∧ lo ≤ e.2 + c e.1 ∧ e.2 + c e.1 ≤ hi}

@[simp] theorem mem_winE {c : α → ℤ} {lo hi : ℤ} {e : α × ℤ} :
    e ∈ winE c lo hi ↔ lo ≤ e.2 ∧ e.2 ≤ hi ∧ lo ≤ e.2 + c e.1 ∧ e.2 + c e.1 ≤ hi := Iff.rfl

/-- **The tree of the window**: the edges of the window of *trivial* loop class.  For the tree-path
gauge these are exactly the edges of the spanning tree. -/
def winTree (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) : Set (α × ℤ) :=
  {e | e ∈ winE c lo hi ∧ coverClassAt Wt c e = 1}

@[simp] theorem mem_winTree {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ} {e : α × ℤ} :
    e ∈ winTree Wt c lo hi ↔ e ∈ winE c lo hi ∧ coverClassAt Wt c e = 1 := Iff.rfl

/-- **The alphabet of the vertex**: the non-tree edges of the window, i.e. the edges of the window of
non-trivial loop class. -/
def winBeta (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) : Type u :=
  {e : α × ℤ // e ∈ winE c lo hi ∧ coverClassAt Wt c e ≠ 1}

theorem winBeta_val_mem {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    (e : winBeta Wt c lo hi) : e.1 ∈ winE c lo hi := e.2.1

theorem winBeta_val_class {Wt : ℤ → FreeGroup α} {c : α → ℤ} {lo hi : ℤ}
    (e : winBeta Wt c lo hi) : coverClassAt Wt c e.1 ≠ 1 := e.2.2

/-- **The class map** `F (β) →* F α` of the vertex: an edge of the window is sent to its loop class
`Wt i · x · (Wt (i + c x))⁻¹`. -/
noncomputable def winRho (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    FreeGroup (winBeta Wt c lo hi) →* FreeGroup α :=
  FreeGroup.lift fun e => coverClassAt Wt c e.1

@[simp] theorem winRho_of (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (e : winBeta Wt c lo hi) :
    winRho Wt c lo hi (FreeGroup.of e) = coverClassAt Wt c e.1 :=
  FreeGroup.lift_apply_of

/-- **The deleted walk word**: the traversals of the walk of `u` whose edge lies in the window and has
non-trivial loop class, read as a word in the alphabet `β`.  The word is *edge-indexed*: the
generator attached to a traversal is its edge, so the two traversals of one edge give the same
generator, carrying the sign of the traversal. -/
noncomputable def winRootList (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α) :
    List (winBeta Wt c lo hi × Bool) := by
  classical
  exact (decor c 0 (wordOf u)).filterMap (fun p : (α × ℤ) × Bool =>
    if h : coverEdge p ∈ winE c lo hi ∧ coverClassAt Wt c (coverEdge p) ≠ 1 then
      some (⟨coverEdge p, h.1, h.2⟩, p.2)
    else none)

/-- **The candidate root** `v ∈ F (β)` of the window decomposition: the word of the deleted walk
word. -/
noncomputable def winRoot (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α) :
    FreeGroup (winBeta Wt c lo hi) :=
  FreeGroup.mk (winRootList Wt c lo hi u)

/-- The sign convention: the `β`-generator of a traversal, raised to the sign of the traversal, has
value the loop class of the *traversal* (not of the edge). -/
theorem winRho_cond_class (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (q : winBeta Wt c lo hi × Bool) :
    (cond q.2 (coverClassAt Wt c q.1.1) (coverClassAt Wt c q.1.1)⁻¹)
      = coverClass Wt c (q.1.1, q.2) := by
  rw [coverClass_eq_signed_coverClassAt]
  cases q.2 <;> rfl

end Work.OROneRel
