import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.TreeDatum
import Submission.Work.ORBassSerre.Action.Structure.BSPresFP
import Submission.Work.ORBassSerre.Action.Structure.Phi_surjective
import Submission.Work.ORBassSerre.Action.Structure.nonempty_presData
import Submission.Work.ORBassSerre.Action.Structure.BSReduction
import Submission.Work.ORBassSerre.Action.Structure.isFinitelyPresented_of_isEmpty_total

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action.Structure

open Quiver

/-!
# A group acting cocompactly and without inversions on a tree is finitely presented

This is the inversion-free case of the target theorem: the canonical map `Φ : Γ →* G` of the
Bass--Serre presentation of the fundamental domain is surjective (`Phi_surjective`) and injective
(`PathWord.Φ_injective`, the walk argument), and `Γ` is finitely presented
(`Gamma_isFinitelyPresented`), so `G` is finitely presented.

The degenerate case in which the tree has no arrows at all (so that there is no path word at all,
hence no presentation) is handled by `isFinitelyPresented_of_isEmpty_total`: then the tree is a
single vertex and `G` is its vertex stabiliser.

The general case (an action with inversions) is reduced to this one by passing to the subgroup of
elements preserving the bipartition of the tree, which is of index at most two.

The hypotheses `[Fintype (orbitV G V)]` and `[Fintype (orbitE G V)]` are the finiteness of the orbit
sets (which follows from `IsCocompact`); they are stated explicitly because the presentation `Gamma`
is built from the *edge* orbits `Work.ORBassSerre.orbitE G V`, whose universe is fixed, so the
statement has to mention them in order to be able to use it.
-/

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-- A group acting cocompactly and without inversions on a non-empty tree, with finitely presented
vertex stabilisers and finitely generated edge stabilisers, is finitely presented. -/
theorem isFinitelyPresented_of_noInversions [Nonempty V] (hT : Work.ORBassSerre.IsTree V)
    (hcc : Work.ORBassSerre.IsCocompact G V) (hninv : Work.ORBassSerre.ActsWithoutInversions G V)
    (hstab : ∀ v : V, Group.IsFinitelyPresented (MulAction.stabilizer G v))
    (hedge : ∀ e : Quiver.Total V, Group.FG (MulAction.stabilizer G e))
    [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)] :
    Group.IsFinitelyPresented G := by
  classical
  by_cases hne : Nonempty (Quiver.Total V)
  · haveI : Finite (Work.ORBassSerre.orbitE G V) := hcc.2
    haveI : Fintype (Work.ORBassSerre.orbitE G V) := Fintype.ofFinite _
    haveI : Nonempty (Work.ORBassSerre.orbitE G V) :=
      ⟨Quotient.mk'' (Classical.choice hne)⟩
    have hneV : Nonempty (Work.ORBassSerre.orbitV G V) :=
      ⟨Quotient.mk'' (Classical.arbitrary V)⟩
    obtain ⟨d⟩ := nonempty_treeDatum (G := G) (V := V) hT hcc hninv (Classical.choice hneV)
    obtain ⟨D⟩ := nonempty_presData d hstab hedge
    haveI : Group.IsFinitelyPresented (d.Gamma D) := d.Gamma_isFinitelyPresented D
    have hinj : Function.Injective (d.Φ D) := TreeDatum.PathWord.Φ_injective D hT
    have hsurj : Function.Surjective (d.Φ D) := Phi_surjective hT d D
    have hker : (d.Φ D).ker.IsFinitelyNormallyGenerated := by
      rw [(MonoidHom.ker_eq_bot_iff (d.Φ D)).mpr hinj]
      exact Subgroup.IsFinitelyNormallyGenerated.bot
    exact Group.IsFinitelyPresented.of_surjective (d.Φ D) hsurj hker
  · exact isFinitelyPresented_of_isEmpty_total (G := G) (V := V) hT
      ⟨fun X => hne ⟨X⟩⟩ hstab

end Work.ORBassSerre.Action.Structure
