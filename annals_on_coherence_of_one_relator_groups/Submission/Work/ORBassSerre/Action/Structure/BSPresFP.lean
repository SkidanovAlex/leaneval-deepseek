import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.BSPresentation

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action.Structure

open Quiver
open Classical

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

namespace TreeDatum

variable [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]

instance finite_presGen (d : TreeDatum G V) (D : PresData d) : Finite (PresGen d D) := by
  haveI : Finite (Work.ORBassSerre.orbitE G V) := Finite.of_fintype _
  haveI : Finite (Work.ORBassSerre.orbitV G V) := Finite.of_fintype _
  unfold PresGen
  infer_instance

/-- The fundamental group of the fundamental domain is finitely presented. -/
theorem Gamma_isFinitelyPresented (d : TreeDatum G V) (D : PresData d) :
    Group.IsFinitelyPresented (Gamma d D) := by
  haveI : Finite (PresGen d D) := finite_presGen d D
  haveI : Finite (rels d D) := (rels_finite d D).to_subtype
  exact inferInstance

end TreeDatum

end Work.ORBassSerre.Action.Structure
