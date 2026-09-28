import Mathlib
import Submission.Work.Thom.tsqHonest

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# Auxiliary definitions for the naturality of the Mayer–Vietoris transgression

This module fixes the vocabulary for the naturality of the Mayer–Vietoris connecting map
(`Work.Cohomology.honestDelta`) under a continuous map `f : X → Y` and the preimage cover:
the restricted map on the overlap `f ⁻¹' U ∩ f ⁻¹' V → U ∩ V`, and the pullback maps on the honest
cohomology used in the statement of `Work.Thom.transgressionNaturalGeneral`.
-/

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Thom

noncomputable section

/-- The restriction of a continuous map `f : X → Y` to the preimage of the overlap `U ∩ V`. -/
def fPieceProj {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (U V : Set Y) : C(↥(f ⁻¹' U ∩ f ⁻¹' V), ↥(U ∩ V)) :=
  ⟨fun p => ⟨f p.1, ⟨p.2.1, p.2.2⟩⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem fPieceProj_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (U V : Set Y) (p : ↥(f ⁻¹' U ∩ f ⁻¹' V)) :
    (fPieceProj f U V p : Y) = f p.1 := rfl

/-- The pullback of the absolute cohomology of the base to the total space, along the projection. -/
abbrev relPb {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (n : ℕ) : Work.Thom.RelCoh ℤ n Y (∅ : Set Y) ⟶ Work.Thom.RelCoh ℤ n X (∅ : Set X) :=
  Work.Thom.relCohMap f (∅ : Set X) (∅ : Set Y) (fun _ h => h) ℤ n

end

end Work.Thom
