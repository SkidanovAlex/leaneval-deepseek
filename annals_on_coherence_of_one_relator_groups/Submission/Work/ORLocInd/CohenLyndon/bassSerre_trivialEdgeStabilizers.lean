import Mathlib
import Submission.Work.ORBassSerre.Interface
import Submission.Work.ORBassSerre.Action.Structure.TreeDatum
import Submission.Work.ORLocInd.FKSKernel.Kurosh.TreeDatum
import Submission.Work.ORLocInd.FKSKernel.vertexStabilizersFreeProductDatum

namespace Work.ORLocInd.CohenLyndon

open Quiver

universe u

/-!
# The Bass--Serre structure theorem with trivial edge stabilisers

A group `Γ` acting on a tree `V` without inversions and with trivial edge stabilisers, whose
vertex stabilisers generate `Γ`, is the free product of the stabilisers of a complete set of
representatives of the vertex orbits (Bass--Serre / Kurosh).

The spanning-tree datum `Work.ORBassSerre.Action.Structure.TreeDatum` of the quotient graph used
by the Breslauer/`Work.ORBassSerre` development and the datum
`Work.ORLocInd.FKSKernel.Kurosh.TreeDatum` used by the `FKSKernel` development have literally
the same fields, so the general result
`Work.ORLocInd.FKSKernel.vertexStabilizersFreeProductDatum` (which is stated for the latter)
applies verbatim once we transport the datum.
-/

/-- The spanning-tree datum of `Work.ORBassSerre.Action.Structure` read as a
`Work.ORLocInd.FKSKernel.Kurosh.TreeDatum`; the two structures have the same fields. -/
def toKuroshTreeDatum {Γ : Type u} {V : Type u} [Group Γ] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction Γ V] [Work.ORBassSerre.GraphAction Γ V]
    (d : Work.ORBassSerre.Action.Structure.TreeDatum Γ V) :
    Work.ORLocInd.FKSKernel.Kurosh.TreeDatum Γ V where
  root := d.root
  vert := d.vert
  par := d.par
  rank := d.rank
  parArrow := d.parArrow
  vert_mk := d.vert_mk
  rank_root := d.rank_root
  rank_eq_zero := d.rank_eq_zero
  rank_par_lt := d.rank_par_lt
  parArrow_left := d.parArrow_left
  parArrow_right := d.parArrow_right
  parArrow_ne := d.parArrow_ne

/-- The vertex lifted by the transported datum is the vertex lifted by the original datum. -/
theorem toKuroshTreeDatum_vert {Γ : Type u} {V : Type u} [Group Γ] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction Γ V] [Work.ORBassSerre.GraphAction Γ V]
    (d : Work.ORBassSerre.Action.Structure.TreeDatum Γ V) :
    (toKuroshTreeDatum d).vert = d.vert := rfl

/-- The vertex group of the transported datum is the stabiliser of the lifted vertex. -/
theorem toKuroshTreeDatum_vgroup {Γ : Type u} {V : Type u} [Group Γ] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction Γ V] [Work.ORBassSerre.GraphAction Γ V]
    (d : Work.ORBassSerre.Action.Structure.TreeDatum Γ V)
    (A : Work.ORBassSerre.orbitV Γ V) :
    (toKuroshTreeDatum d).vgroup A = MulAction.stabilizer Γ (d.vert A) := rfl

theorem bassSerre_trivialEdgeStabilizers {Γ : Type u} {V : Type u} [Group Γ]
    [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction Γ V]
    [Work.ORBassSerre.GraphAction Γ V]
    (d : Work.ORBassSerre.Action.Structure.TreeDatum Γ V)
    (hT : Work.ORBassSerre.IsTree V) (hninv : Work.ORBassSerre.ActsWithoutInversions Γ V)
    (hedge : ∀ e : Quiver.Total V, MulAction.stabilizer Γ e = ⊥)
    (hgen : Subgroup.closure (⋃ v : V, (MulAction.stabilizer Γ v : Set Γ)) = ⊤) :
    ∃ e : Monoid.CoprodI (fun A : Work.ORBassSerre.orbitV Γ V =>
        ↥(MulAction.stabilizer Γ (d.vert A))) ≃* Γ,
      ∀ (A : Work.ORBassSerre.orbitV Γ V) (z : ↥(MulAction.stabilizer Γ (d.vert A))),
        e (Monoid.CoprodI.of z) = (z : Γ) := by
  obtain ⟨e, he⟩ :=
    Work.ORLocInd.FKSKernel.vertexStabilizersFreeProductDatum (Γ := Γ) (V := V)
      hT hninv hedge hgen (toKuroshTreeDatum d)
  exact ⟨e, he⟩

end Work.ORLocInd.CohenLyndon
