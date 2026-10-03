/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The Serre §5 quotient tree, as a construction

`Hypotheses.SerreQuotientTree` asks for the quotient of an `H`-tree `S'` by the normal closure
`K` of a finite family of vertex subgroups, in the exact form of Serre §5 / JL Lemma 4.1: the
quotient map is `Quotient.mk''` onto the set of `K`-orbits of vertices, *every* edge of the
quotient comes from an edge of `S'`, and the fibres of the quotient map are exactly the
`K`-orbits.

This file isolates the *construction* so that the individual clauses can be proved (and
reused) one at a time.  The vertex set is `W ⧸ K`, with the action of `H ⧸ K` induced by the
`H`-action (`Work.ORBassSerre.instMulActionQuotientOrbit`); the graph is the underlying simple
graph of the quotient quiver of the `K`-action on the edge quiver of `S'`
(`Work.ORDunwoody.Lemmas.quiverGraph` of `Work.ORBassSerre.orbitQuiver`); it is a tree by JL
Lemma 4.1, `Work.ORBassSerre.Action.isTree_orbitV_of_normalClosure_elliptic`, which applies
precisely under the hypothesis that `K` is the normal closure of a set of elliptic elements.

Owner: node N12 ("G-trees and quotient graphs", "JL Lemma 4.1").
-/
import Mathlib
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORBassSerre.Action.isTree_orbitV_of_normalClosure_elliptic
import Submission.Work.ORDunwoody.Lemmas.GraphQuiver
import Submission.Work.ORDunwoody.Lemmas.GraphQuiverTree
import Submission.Work.ORDunwoody.Lemmas.ofQuiverTree
import Submission.Work.ORBassSerre.QuotientTree.nonempty_hom_smul

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open Work.ORBassSerre

/-- **The Serre §5 quotient tree.**  For an `H`-tree `S'` and a normal subgroup `K ▁ H` which
is the normal closure of a set `E` of elliptic elements of the action of `H` on `S'`, the
quotient tree has vertex set the set `W ⧸ K` of `K`-orbits of vertices of `S'`, on which
`H ⧸ K` acts through the quotient action, and edge set the set of `K`-orbits of edges of `S'`
(the quotient quiver of the `K`-action on the edge quiver of `S'`).

This is an `abbrev` so that its underlying graph is visible to definitional equality: the
adjacency relation of the quotient tree is, by definition, the existence of an arrow of the
quotient quiver, `Nonempty (x ⟶ y)`. -/
noncomputable abbrev quotientTreeOfNormalClosure {H : Type u} [Group H] {W : Type u}
    [MulAction H W] (S' : Work.ORDunwoody.GTree H W) (K : Subgroup H) [K.Normal] (E : Set H)
    (hEll : ∀ g ∈ E, ∃ v : W, g • v = v) (hgen : Subgroup.normalClosure E = K) :
    Work.ORDunwoody.GTree (H ⧸ K) (MulAction.orbitRel.Quotient ↥K W) := by
  classical
  letI : Quiver W := Work.ORDunwoody.Lemmas.graphQuiver S'.graph
  letI : Quiver.HasInvolutiveReverse W :=
    Work.ORDunwoody.Lemmas.graphQuiverHasInvolutiveReverse S'.graph
  letI : Work.ORBassSerre.GraphAction H W := Work.ORDunwoody.Lemmas.graphQuiverAction S'
  have hT : Work.ORBassSerre.IsTree W := Work.ORDunwoody.Lemmas.graphQuiver_isTree S'
  haveI : Nonempty W := S'.isTree.connected.nonempty
  have htree : Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV ↥K W) :=
    Work.ORBassSerre.Action.isTree_orbitV_of_normalClosure_elliptic hT K E hEll hgen
  haveI : Nonempty (Work.ORBassSerre.orbitV ↥K W) :=
    (inferInstance : Nonempty W).map Quotient.mk''
  have hnl : ∀ X : Work.ORBassSerre.orbitV ↥K W, ¬ Nonempty (X ⟶ X) :=
    Work.ORDunwoody.Lemmas.noLoop_of_isTree htree
  exact
    { graph := Work.ORDunwoody.Lemmas.quiverGraph (Work.ORBassSerre.orbitV ↥K W) hnl
      isTree := Work.ORDunwoody.Lemmas.isTree_quiverGraph htree
      smul_adj := fun q _ _ h => Work.ORBassSerre.QuotientTree.nonempty_hom_smul K h q }

end Work.ORDunwoody
