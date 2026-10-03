import Mathlib
import Submission.Work.ORBassSerre.Interface
import Submission.Work.ORBassSerre.Action.Structure.exists_link
import Submission.Work.ORLocInd.CohenLyndon.bsSetup
import Submission.Work.ORLocInd.FKSKernel.Kurosh.TreeDatum
import Submission.Work.ORLocInd.FKSKernel.Kurosh.closure_vgroup_eq_top

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.CohenLyndon

open Quiver

variable {Γ : Type u} {V : Type u} [Group Γ] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction Γ V] [Work.ORBassSerre.GraphAction Γ V]

/-- The chosen edge lift of an arrow of the quotient graph: for tree edge orbits the plumbing
arrow, otherwise the inverse of the plumbing arrow of the reversed orbit. -/
noncomputable def bsLift (d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum Γ V) :
    (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V :=
  fun A B e => by
    classical
    exact if d.IsTreeEdge (e.1) then d.elift (e.1)
      else (d.elift (Work.ORBassSerre.orbitEReverse (e.1))).reverse

/-- **The lift data of the Bass--Serre structure theorem.**  If `Γ` acts on a tree `V` without
inversions and the quotient graph `V/Γ` is a tree, then there is a section `x` of the vertex
orbits and, for every arrow `e : A ⟶ B` of the quotient graph, an arrow of `V` from `x A` to
`x B` whose orbit is `e`. -/
theorem bsLiftData [Nonempty V] (hT : Work.ORBassSerre.IsTree V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions Γ V)
    (hquot : Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV Γ V)) :
    ∃ x : Work.ORBassSerre.orbitV Γ V → V,
      (∀ A, Quotient.mk'' (x A) = A) ∧
      ∃ L : (A B : Work.ORBassSerre.orbitV Γ V) → (A ⟶ B) → Quiver.Total V,
        (∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
          Quotient.mk'' (L A B e) = e.1 ∧ (L A B e).left = x A ∧ (L A B e).right = x B) ∧
        (∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
          L B A (Quiver.reverse e) = (L A B e).reverse) := by
  classical
  obtain ⟨d⟩ := Work.ORLocInd.FKSKernel.Kurosh.nonempty_treeDatum (G := Γ) (V := V) hT hninv
    (Quotient.mk'' (Classical.choice (inferInstance : Nonempty V)))
  have hprop : ∀ (A B : Work.ORBassSerre.orbitV Γ V) (e : A ⟶ B),
      Quotient.mk'' (bsLift d A B e) = e.1 ∧ (bsLift d A B e).left = d.vert A ∧
        (bsLift d A B e).right = d.vert B := by
    intro A B e
    by_cases h : d.IsTreeEdge (e.1)
    · rw [bsLift, if_pos h]
      refine ⟨d.elift_orbit (e.1), ?_, ?_⟩
      · rw [d.elift_left (e.1), srcE_hom e]
      · rw [d.elift_right (e.1), d.sElt_eq_one h, one_smul, tgtE_hom e]
    · rw [bsLift, if_neg h]
      have h' : d.IsTreeEdge (Work.ORBassSerre.orbitEReverse (e.1)) :=
        (d.isTreeEdge_or_isTreeEdge_orbitEReverse hquot (e.1)).resolve_left h
      refine ⟨?_, ?_, ?_⟩
      · rw [← Work.ORBassSerre.orbitEReverse_mk (e := d.elift
            (Work.ORBassSerre.orbitEReverse (e.1))), d.elift_orbit]
        exact Work.ORBassSerre.orbitEReverse_involutive (e.1)
      · rw [Quiver.Total.reverse_left, d.elift_right, d.sElt_eq_one h', one_smul,
          Work.ORBassSerre.Action.Structure.tgtE_orbitEReverse, srcE_hom e]
      · rw [Quiver.Total.reverse_right, d.elift_left,
          Work.ORBassSerre.Action.Structure.srcE_orbitEReverse, tgtE_hom e]
  refine ⟨fun A => d.vert A, fun A => d.vert_mk A, bsLift d, hprop, ?_⟩
  intro A B e
  refine total_eq_of_isTree hT ?_ ?_
  · rw [Quiver.Total.reverse_left]
    exact (hprop B A (Quiver.reverse e)).2.1.trans (hprop A B e).2.2.symm
  · rw [Quiver.Total.reverse_right]
    exact (hprop B A (Quiver.reverse e)).2.2.trans (hprop A B e).2.1.symm

end Work.ORLocInd.CohenLyndon
