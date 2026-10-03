/-
Copyright: work of the ORDunwoody subproject (node N13).

# From a simplicial tree with a group action to a Bass--Serre tree

`Work.ORDunwoody.GTree G V` is a `SimpleGraph` tree on `V` with a `G`-action preserving
adjacency; `Work.ORBassSerre.IsTree V` is the Bass--Serre (quiver-theoretic) notion of a
tree, for a quiver with an involutive reversal of arrows.  This file shows that the edge
quiver `graphQuiver T.graph` of `T` is a Bass--Serre tree, on which `G` acts compatibly
(`Work.ORBassSerre.GraphAction`), and that the two notions of cocompactness agree.
-/
import Mathlib
import Submission.Work.ORDunwoody.Basic
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORDunwoody.Lemmas.GraphQuiver
import Submission.Work.ORDunwoody.Lemmas.backtrackFreeWalk
import Submission.Work.ORDunwoody.Lemmas.GraphQuiverTree

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u x

namespace Work.ORDunwoody.Lemmas

open SimpleGraph

variable {V : Type u}

/-- **The edge quiver of a `G`-tree is a Bass--Serre `G`-tree.** -/
theorem ofGTree_quiverTree {G : Type*} [Group G] {V : Type*} [MulAction G V]
    (T : Work.ORDunwoody.GTree G V) :
    ∃ (Q : Quiver V) (hR : @Quiver.HasInvolutiveReverse V Q)
      (hA : @Work.ORBassSerre.GraphAction G V _ Q hR.toHasReverse _),
      @Work.ORBassSerre.IsTree V Q hR ∧
      (∀ u v : V, Nonempty (@Quiver.Hom V Q u v) ↔ T.Adj u v) ∧
      (@Work.ORBassSerre.IsCocompact G V _ Q hR.toHasReverse _ hA ↔ T.IsCocompact) := by
  refine ⟨graphQuiver T.graph, graphQuiverHasInvolutiveReverse T.graph, graphQuiverAction T,
    ?_, ?_, ?_⟩
  · exact graphQuiver_isTree T
  · intro u v
    exact nonempty_hom_iff_adj T.graph u v
  · exact graphQuiver_isCocompact_iff T

end Work.ORDunwoody.Lemmas
