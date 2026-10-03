import Mathlib
import Submission.Work.ORLocInd.CoprodTree.StarTreeIsTree
import Submission.Work.ORBassSerre.Action.Structure.TreeDatum
import Submission.Work.ORBassSerre.Action.CoprodI.coprodI_congr
import Submission.Work.ORLocInd.CohenLyndon.spanTreeLift

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Quiver
open Work.ORLocInd.CoprodTree

namespace Work.ORLocInd.CohenLyndon

universe u

/-- **A spanning-tree lift datum exists for any action on a tree.** -/
theorem nonempty_treeDatum_of_tree {G : Type u} {V : Type u} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V) (hninv : Work.ORBassSerre.ActsWithoutInversions G V)
    (root : Work.ORBassSerre.orbitV G V) :
    Nonempty (Work.ORBassSerre.Action.Structure.TreeDatum G V) := by
  obtain ⟨vert, par, rank, parArrow, h1, h2, h3, h4, h5, h6⟩ :=
    Span.exists_spanningTree_lift (G := G) (V := V) hT hninv root
  exact ⟨root, vert, par, rank, parArrow, h1, h2, h3, h4,
    fun A hA => (h5 A hA).1, fun A hA => (h5 A hA).2, h6⟩

end Work.ORLocInd.CohenLyndon
