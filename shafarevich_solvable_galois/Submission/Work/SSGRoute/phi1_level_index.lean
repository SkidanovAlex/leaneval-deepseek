import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester): read `DESIGN_FIX.md` §1 and the "colimit step"
section of `PHI1_PGROUP_STATUS.md`.

# The level index for the colimit step of E5s

The colimit step of `Work.SSGRoute.phi1_mono_step_in` (`exists_realization_of_delta_lam`) needs the
finite Galois levels `K ≤ L ≤ Ω` as an *index type* of a direct limit.  This file provides:

* `Lvl k K Ω` — the finite Galois levels, with the instances `NumberField`, `FiniteDimensional k`,
  `IsGalois k` recovered from the subtype, and the inherited `Preorder`;
* `Nonempty (Lvl k K Ω)` — witnessed by the bottom level `K` (via `IntermediateField.botEquiv`
  and `IsGalois.of_algEquiv`).

* `IsDirectedOrder (Lvl k K Ω)` — the compositum of two levels is a level, via `isGalois_sup`,
  `IntermediateField.finiteDimensional_sup` and the tower of finite extensions; and `isGalois_sup`
  (the compositum of two Galois levels is Galois, transported from the Mathlib instances over
  `IntermediateField k Ω` across the canonical `AlgEquiv` of the two carriers). -/

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- The **finite Galois levels** `K ≤ L ≤ Ω`. -/
abbrev Lvl (k K Ω : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] : Type _ :=
  {L : IntermediateField K Ω // NumberField L ∧ FiniteDimensional k L ∧ IsGalois k L}

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

/-- **The compositum of two Galois levels is Galois.**  Mathlib gives `Algebra.IsSeparable` and
`Normal` for the compositum *inside* `IntermediateField k Ω`
(`IntermediateField.isSeparable_sup`, `normal_sup`); `IntermediateField.restrictScalars_sup` and
`IntermediateField.coe_restrictScalars` identify the carriers, and the canonical `AlgEquiv`
(identity on the carrier) transports `IsGalois k` to the compositum taken in
`IntermediateField K Ω`. -/
theorem isGalois_sup {L L' : IntermediateField K Ω} [IsGalois k L] [IsGalois k L'] :
    IsGalois k ↥(L ⊔ L') := by
  haveI h1 : Algebra.IsSeparable k ↥(IntermediateField.restrictScalars k L) :=
    (isGalois_iff.mp (inferInstance : IsGalois k L)).1
  haveI h1' : Normal k ↥(IntermediateField.restrictScalars k L) :=
    (isGalois_iff.mp (inferInstance : IsGalois k L)).2
  haveI h2 : Algebra.IsSeparable k ↥(IntermediateField.restrictScalars k L') :=
    (isGalois_iff.mp (inferInstance : IsGalois k L')).1
  haveI h2' : Normal k ↥(IntermediateField.restrictScalars k L') :=
    (isGalois_iff.mp (inferInstance : IsGalois k L')).2
  haveI hgal : IsGalois k
      ↥((IntermediateField.restrictScalars k L) ⊔ (IntermediateField.restrictScalars k L')) :=
    isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hset : (((IntermediateField.restrictScalars k L) ⊔ (IntermediateField.restrictScalars k L')
        : IntermediateField k Ω) : Set Ω) = (((L ⊔ L') : IntermediateField K Ω) : Set Ω) := by
    rw [IntermediateField.restrictScalars_sup k L L']
    exact IntermediateField.coe_restrictScalars k
  let e : ↥((IntermediateField.restrictScalars k L) ⊔ (IntermediateField.restrictScalars k L'))
      ≃ₐ[k] ↥(L ⊔ L') :=
    { toFun := fun x => ⟨x.1, by
        have hx : (x : Ω) ∈ (((IntermediateField.restrictScalars k L) ⊔
            (IntermediateField.restrictScalars k L') : IntermediateField k Ω) : Set Ω) := x.2
        rwa [hset] at hx⟩
      invFun := fun y => ⟨y.1, by
        have hy : (y : Ω) ∈ ((L ⊔ L' : IntermediateField K Ω) : Set Ω) := y.2
        rwa [← hset] at hy⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl
      commutes' := fun a => Subtype.ext rfl }
  exact IsGalois.of_algEquiv e

namespace Lvl

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

instance instNumberField (L : Lvl k K Ω) : NumberField ↥L.1 := L.2.1

instance instFiniteDimensional (L : Lvl k K Ω) : FiniteDimensional k ↥L.1 := L.2.2.1

instance instIsGalois (L : Lvl k K Ω) : IsGalois k ↥L.1 := L.2.2.2

/-- **The levels are a directed set**: the upper bound of two levels is their compositum
(`IntermediateField.finiteDimensional_sup`, `isGalois_sup`, and the tower of finite extensions for
`NumberField`). -/
instance instIsDirectedOrderLvl [IsGalois k K] : IsDirectedOrder (Lvl k K Ω) where
  directed a b := by
    haveI hfd : FiniteDimensional K ↥(a.1 ⊔ b.1) :=
      IntermediateField.finiteDimensional_sup a.1 b.1
    have hgal : IsGalois k ↥(a.1 ⊔ b.1) := isGalois_sup (L := a.1) (L' := b.1)
    exact ⟨⟨a.1 ⊔ b.1, inferInstance, inferInstance, hgal⟩,
      (show a.1 ≤ a.1 ⊔ b.1 from le_sup_left),
      (show b.1 ≤ a.1 ⊔ b.1 from le_sup_right)⟩

/-- **The levels are nonempty**: the bottom level `K`. -/
instance instNonempty [IsGalois k K] : Nonempty (Lvl k K Ω) :=
  ⟨⟨⊥, inferInstance, inferInstance,
    IsGalois.of_algEquiv ((IntermediateField.botEquiv K Ω).symm.restrictScalars k)⟩⟩

end Lvl

end Work.SSGRoute
