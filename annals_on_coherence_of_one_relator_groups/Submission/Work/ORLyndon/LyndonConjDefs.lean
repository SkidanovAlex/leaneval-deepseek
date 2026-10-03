import Mathlib
import Submission.Work.ORLyndon.LyndonIndependenceDefs
import Submission.Work.ORLyndon.Fox

/-!
# Conjugating the one-relator presentation

Let `X` be a type, `c : F(X)` an element of the free group, `K` a field and `r : F(X)` a relator.
Conjugating the relator does not change the presented group up to isomorphism:
`⟨X | c r c⁻¹⟩ ≅ ⟨X | r⟩`, via the map induced by `w ↦ c w c⁻¹`.

This file records the two mutually inverse group homomorphisms of the presentations,

* `Work.ORLyndon.conjHom r c : ⟨X | r⟩ →* ⟨X | c r c⁻¹⟩`, induced by `w ↦ c w c⁻¹`,
* `Work.ORLyndon.conjHomInv r c : ⟨X | c r c⁻¹⟩ →* ⟨X | r⟩`, induced by `w ↦ c⁻¹ w c`,

together with their effect on the canonical surjections `presentRho` and the two inverse laws.  This
is the device along which the conjugation invariance of the Cohen--Lyndon independence statement
(`Work.ORLyndon.LyndonIndependence`, in `lyndonIndependence_conj.lean`) is transported.

## Main definitions

* `Work.ORLyndon.conjAut` -- the conjugating automorphism `w ↦ c * w * c⁻¹` of `F(X)`.
* `Work.ORLyndon.conjHom`, `Work.ORLyndon.conjHomInv` -- the induced maps of the presentations.

## Main results

* `Work.ORLyndon.conjHom_mk` -- `conjHom r c (presentRho r w) = presentRho (c r c⁻¹) (c w c⁻¹)`;
* `Work.ORLyndon.conjHomInv_mk` -- the analogous statement for `conjHomInv`;
* `Work.ORLyndon.conjHomInv_conjHom`, `Work.ORLyndon.conjHom_conjHomInv` -- the two maps are
  mutually inverse.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

variable {X : Type u} {K : Type v}

section Conj

variable [DecidableEq X]

/-- The conjugating automorphism `w ↦ c * w * c⁻¹` of the free group `F(X)`, as a monoid
homomorphism. -/
noncomputable def conjAut (c : FreeGroup X) : FreeGroup X →* FreeGroup X :=
  (MulAut.conj c).toMonoidHom

@[simp] theorem conjAut_apply (c w : FreeGroup X) : conjAut c w = c * w * c⁻¹ :=
  MulAut.conj_apply c w

/-- **The homomorphism of presentations induced by conjugation of the relator.**  Sending a word
`w` to `c * w * c⁻¹` maps the relator `r` to `c * r * c⁻¹`, hence induces a group homomorphism
`⟨X | r⟩ →* ⟨X | c * r * c⁻¹⟩`. -/
noncomputable def conjHom (r c : FreeGroup X) :
    OneRelatorGroup r →* OneRelatorGroup (c * r * c⁻¹) :=
  QuotientGroup.lift (Subgroup.normalClosure ({r} : Set (FreeGroup X)))
    ((PresentedGroup.mk {c * r * c⁻¹}).comp (conjAut c)) (by
      refine Subgroup.normalClosure_le_normal ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      show (PresentedGroup.mk {c * r * c⁻¹}) (conjAut c r) = 1
      rw [conjAut_apply]
      exact PresentedGroup.one_of_mem (Set.mem_singleton _))

/-- **The inverse of `conjHom`**: sending a word `w` to `c⁻¹ * w * c` maps the relator
`c * r * c⁻¹` to `r`, hence induces a group homomorphism
`⟨X | c * r * c⁻¹⟩ →* ⟨X | r⟩`. -/
noncomputable def conjHomInv (r c : FreeGroup X) :
    OneRelatorGroup (c * r * c⁻¹) →* OneRelatorGroup r :=
  QuotientGroup.lift (Subgroup.normalClosure ({c * r * c⁻¹} : Set (FreeGroup X)))
    ((PresentedGroup.mk {r}).comp (conjAut c⁻¹)) (by
      refine Subgroup.normalClosure_le_normal ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      show (PresentedGroup.mk {r}) (conjAut c⁻¹ (c * r * c⁻¹)) = 1
      rw [conjAut_apply]
      have h1 : c⁻¹ * (c * r * c⁻¹) * (c⁻¹)⁻¹ = r := by group
      rw [h1]
      exact PresentedGroup.one_of_mem (Set.mem_singleton _))

/-- `conjHom` on the canonical elements: `presentRho r w ↦ presentRho (c r c⁻¹) (c w c⁻¹)`. -/
theorem conjHom_mk (r c w : FreeGroup X) :
    conjHom r c (presentRho r w) = presentRho (c * r * c⁻¹) (c * w * c⁻¹) := by
  show (QuotientGroup.lift (Subgroup.normalClosure ({r} : Set (FreeGroup X)))
      ((PresentedGroup.mk {c * r * c⁻¹}).comp (conjAut c)) _) (QuotientGroup.mk w)
      = QuotientGroup.mk (c * w * c⁻¹)
  rw [QuotientGroup.lift_mk, MonoidHom.comp_apply, conjAut_apply]
  exact rfl

/-- `conjHomInv` on the canonical elements: `presentRho (c r c⁻¹) w ↦ presentRho r (c⁻¹ w c)`. -/
theorem conjHomInv_mk (r c w : FreeGroup X) :
    conjHomInv r c (presentRho (c * r * c⁻¹) w) = presentRho r (c⁻¹ * w * c) := by
  show (QuotientGroup.lift (Subgroup.normalClosure ({c * r * c⁻¹} : Set (FreeGroup X)))
      ((PresentedGroup.mk {r}).comp (conjAut c⁻¹)) _) (QuotientGroup.mk w)
      = QuotientGroup.mk (c⁻¹ * w * c)
  rw [QuotientGroup.lift_mk, MonoidHom.comp_apply, conjAut_apply, inv_inv]
  exact rfl

/-- The two maps of presentations are mutually inverse, first composite. -/
theorem conjHomInv_conjHom (r c : FreeGroup X) (g : OneRelatorGroup r) :
    conjHomInv r c (conjHom r c g) = g := by
  refine PresentedGroup.induction_on
    (C := fun x => conjHomInv r c (conjHom r c x) = x) g ?_
  intro w
  change conjHomInv r c (conjHom r c (presentRho r w)) = presentRho r w
  rw [conjHom_mk, conjHomInv_mk]
  congr 1
  group

/-- The two maps of presentations are mutually inverse, second composite. -/
theorem conjHom_conjHomInv (r c : FreeGroup X) (g : OneRelatorGroup (c * r * c⁻¹)) :
    conjHom r c (conjHomInv r c g) = g := by
  refine PresentedGroup.induction_on
    (C := fun x => conjHom r c (conjHomInv r c x) = x) g ?_
  intro w
  change conjHom r c (conjHomInv r c (presentRho (c * r * c⁻¹) w))
    = presentRho (c * r * c⁻¹) w
  rw [conjHomInv_mk, conjHom_mk]
  congr 1
  group

end Conj

end Work.ORLyndon
