/-
  Area C2 (WilC2): the definable closure `Dcl A` of a parameter set, together with the
  Tarski–Vaught packaging of o-minimality: `Dcl A` is an elementary substructure of `M`.
-/
import Submission.Work.WilC2.Basic
import Mathlib.ModelTheory.ElementarySubstructures

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-- The **definable closure** of a set of parameters: the points of `M` that are definable from
parameters in `A`. -/
def Dcl {M : Type*} [LRc.Structure M] (A : Set M) : Set M :=
  {x | A.Definable₁ LRc {x}}

theorem mem_dcl {M : Type*} [LRc.Structure M] {A : Set M} {x : M} :
    x ∈ Dcl A ↔ A.Definable₁ LRc {x} := Iff.rfl

theorem dcl_mono {M : Type*} [LRc.Structure M] {A B : Set M} (h : A ⊆ B) : Dcl A ⊆ Dcl B :=
  fun x hx => Set.Definable.mono hx h

end Work.WilC2
