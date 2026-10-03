import Mathlib
import Submission.Work.ORAssembly.Defs
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORBassSerre.Interface
import Submission.Work.ORDunwoody.Lemmas.ofGTree_quiverTree
import Submission.Work.ORDunwoody.Lemmas.GraphQuiver
import Submission.Work.ORDunwoody.Lemmas.GraphQuiverTree
import Submission.Work.ORBassSerre.Action.isFinitelyPresented_of_isCocompact_tree

set_option linter.style.haveILetI false

namespace Work.ORBassSerre.Assembly

universe u

/-- Node N12 discharging `Work.ORDunwoody.BassSerreFinitelyPresentedAll`: a group acting
cocompactly on a tree with finitely generated edge stabilizers and finitely presented vertex
stabilizers is finitely presented.  (`Work.ORDunwoody.GTree` forces the tree to be non-empty, so
the statement is not vacuous.)  Use the bridge `Work.ORDunwoody.Lemmas.ofGTree_quiverTree`
together with `Work.ORBassSerre.Action.isFinitelyPresented_of_isCocompact_tree`. -/
theorem bassSerreFinitelyPresentedAll (X : Type u) :
    Work.ORDunwoody.BassSerreFinitelyPresentedAll X := by
  intro G _ V _ T hcc hedge hstab
  -- Read the simplicial tree `T` as a Bass--Serre tree: its edge quiver is the quiver
  -- `graphQuiver T.graph` with the lifted reversal and the induced graph action.
  letI : Quiver.{u, u} V := Work.ORDunwoody.Lemmas.graphQuiver T.graph
  letI : Quiver.HasReverse V := Work.ORDunwoody.Lemmas.graphQuiverHasReverse T.graph
  letI : Quiver.HasInvolutiveReverse V :=
    Work.ORDunwoody.Lemmas.graphQuiverHasInvolutiveReverse T.graph
  letI : Work.ORBassSerre.GraphAction G V := Work.ORDunwoody.Lemmas.graphQuiverAction T
  -- `GTree` is connected, hence the vertex type is non-empty.
  haveI : Nonempty V := T.isTree.connected.nonempty
  -- The stabiliser of an arrow of the edge quiver is the (setwise) stabiliser of its two
  -- endpoints, i.e. the edge stabiliser of the simplicial tree (arrows between two vertices
  -- form a subsingleton, so fixing both endpoints fixes the arrow).
  have key : ∀ e : Quiver.Total V, MulAction.stabilizer G e = T.edgeStab e.left e.right := by
    intro e
    ext g
    rw [MulAction.mem_stabilizer_iff, Work.ORDunwoody.GTree.edgeStab_eq, Subgroup.mem_inf,
      Work.ORDunwoody.GTree.vertexStab, Work.ORDunwoody.GTree.vertexStab,
      MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      exact ⟨(Work.ORBassSerre.GraphAction.smul_left g e).symm.trans
                (congrArg Quiver.Total.left h),
             (Work.ORBassSerre.GraphAction.smul_right g e).symm.trans
                (congrArg Quiver.Total.right h)⟩
    · rintro ⟨h1, h2⟩
      refine Quiver.Total.ext ?_ ?_ ?_
      · exact (Work.ORBassSerre.GraphAction.smul_left g e).trans h1
      · exact (Work.ORBassSerre.GraphAction.smul_right g e).trans h2
      · refine Subsingleton.helim ?_ _ _
        show (g • e.left ⟶ g • e.right) = (e.left ⟶ e.right)
        rw [h1, h2]
  -- Finitely generated edge stabilisers of `T` are finitely generated arrow stabilisers.
  have hedge' : ∀ e : Quiver.Total V, Group.FG (MulAction.stabilizer G e) := by
    intro e
    rw [key e]
    exact (Group.fg_iff_subgroup_fg _).mpr (hedge e.left e.right e.hom.down.2)
  exact Work.ORBassSerre.Action.isFinitelyPresented_of_isCocompact_tree
    (Work.ORDunwoody.Lemmas.graphQuiver_isTree T)
    ((Work.ORDunwoody.Lemmas.graphQuiver_isCocompact_iff T).mpr hcc)
    (fun v => hstab v) hedge'

end Work.ORBassSerre.Assembly
