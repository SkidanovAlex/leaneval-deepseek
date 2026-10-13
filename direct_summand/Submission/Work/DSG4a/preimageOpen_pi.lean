import Mathlib
import Submission.Work.DSG4a.BaseChange

namespace Work.DSG4a

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

section Helpers

variable {X X' : Scheme.{u}}

/-- In the complete lattice `X.Opens`, the categorical product of a finite family is the
infimum.  (This is the general statement that products in a poset are greatest lower bounds,
specialised to `Opens`; both sides are `glb`s of `Set.range V`.) -/
lemma piObj_opens_eq_iInf {ι : Type u} [Fintype ι] (V : ι → X.Opens) :
    (∏ᶜ V : X.Opens) = iInf V := by
  refine le_antisymm (le_iInf fun i => (Pi.π V i).le) ?_
  exact (Pi.lift fun i => homOfLE (iInf_le V i)).le

/-- Preimage of opens commutes with finite infima: `g ⁻¹ᵁ ⨅ i, U i = ⨅ i, g ⁻¹ᵁ U i`.
This is where finiteness is used — `Opens.coe_iInf` says that the underlying set of a finite
infimum of opens is the (finite) intersection. -/
lemma preimage_iInf_opens {ι : Type u} [Finite ι] (g : X' ⟶ X) (U : ι → X.Opens) :
    (TopologicalSpace.Opens.map g.base).obj (iInf U) =
      iInf fun i => (TopologicalSpace.Opens.map g.base).obj (U i) := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_preimage, TopologicalSpace.Opens.coe_iInf]
  exact Set.preimage_iInter

end Helpers

theorem preimageOpen_pi {X X' : Scheme.{u}} (g : X' ⟶ X) {α : Type u} [Fintype α]
    (V : α → X.Opens) :
    Work.DSG4a.preimageOpen g (∏ᶜ V) = ∏ᶜ (fun a => Work.DSG4a.preimageOpen g (V a)) := by
  have h2 : (∏ᶜ V : X.Opens) = iInf V := piObj_opens_eq_iInf V
  have h3 : (∏ᶜ fun a => (TopologicalSpace.Opens.map g.base).obj (V a) : X'.Opens) =
      iInf (fun a => (TopologicalSpace.Opens.map g.base).obj (V a)) :=
    piObj_opens_eq_iInf _
  have h4 : (TopologicalSpace.Opens.map g.base).obj (iInf V) =
      iInf (fun a => (TopologicalSpace.Opens.map g.base).obj (V a)) :=
    preimage_iInf_opens g V
  unfold preimageOpen
  rw [h2, h4, h3]

end Work.DSG4a
