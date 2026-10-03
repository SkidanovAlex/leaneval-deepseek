import Mathlib
import Submission.Work.ORBassSerre.Tree.Seg.smul_eq_self_of_mem_reducedSpan
import Submission.Work.ORBassSerre.Tree.Geodesic.exists_cons_geodesic_of_ne
import Submission.Work.ORBassSerre.Action.Structure.fpHelpers
import Submission.Work.ORLocInd.FKSKernel.Kurosh.RepProjection

namespace Work.ORLocInd.FKSKernel.Kurosh

/-!
# Elliptic elements of a group acting on a tree with trivial edge stabilisers

Let a group `G` act on a tree `V` (a `Quiver` with involutive reversal satisfying
`Work.ORBassSerre.IsTree`), with trivial stabiliser of every arrow.  Then an element `g ≠ 1`
fixes *at most one* vertex.

The proof is the classical one.  If `g` fixes two distinct vertices `x ≠ y`, the (unique) reduced
path between them has a final arrow `e : c ⟶ y`, and `g` fixes `x` and `y`.  Since the translation
of a reduced path by a graph automorphism is again reduced and has the same endpoints, uniqueness
of reduced paths forces the fixed point set to contain the whole geodesic segment from `x` to `y`
(`Work.ORBassSerre.Tree.Seg.smul_eq_self_of_mem_reducedSpan`); in particular `g` fixes the
endpoints of the arrow `e`, and triviality of the edge stabilisers gives `g = 1`.
-/

universe u

/-- **An element of a group acting on a tree with trivial edge stabilisers fixes at most one
vertex.**  Equivalently: the fixed point set of a non-trivial elliptic element of such an action is
a single vertex (or empty). -/
theorem eq_of_smul_eq_self {G : Type u} {V : Type u} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V)
    (hedge : ∀ e : Quiver.Total V, MulAction.stabilizer G e = ⊥)
    {g : G} (hg : g ≠ 1) {x y : V} (hx : g • x = x) (hy : g • y = y) :
    x = y := by
  by_contra hxy
  -- the geodesic from `x` to `y` is nonempty; take its final arrow `e : c ⟶ y`
  obtain ⟨c, q, e, _, hc⟩ :=
    Work.ORBassSerre.Tree.Geodesic.exists_cons_geodesic_of_ne (V := V) hT hxy
  -- `c` lies on the geodesic segment from `x` to `y`, hence (being between two fixed points) is
  -- itself fixed by `g`
  have hc' : g • c = c :=
    Work.ORBassSerre.Tree.Seg.smul_eq_self_of_mem_reducedSpan (G := G) (V := V) hT hx hy hc
  -- so `g` fixes both endpoints of the arrow `e`, hence lies in its (trivial) stabiliser
  exact hg (Work.ORBassSerre.Action.Structure.FP.eq_one_of_fixes_edge_endpoints
    (Γ := G) (V := V) hT hedge e hc' hy)

end Work.ORLocInd.FKSKernel.Kurosh
