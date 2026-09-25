import Mathlib
import Submission.NK.BrauerTwist.All
import Submission.NK.HassePrinciple.KummerLevel
import Submission.NK.HassePrinciple.UnitsLevel
import Submission.NK.HassePrinciple.MuLevel
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.MuColimit

/-!
# The level dictionary `LevelGroup ⊤ L ≃* Gal(L/K)` and the units transport

This module isolates the (definite) transport used by the finite-support development: the level
group `Gal(K'/K)/Gal(K'/L)` of the full absolute Galois group at a finite Galois level `L` is
`Gal(L/K)` by restriction (`levelGroupEquivTop`), and this identifies the level cohomology
`H²(LevelGroup ⊤ L, Lˣ)` with the group cohomology `H²(Gal(L/K), Lˣ)` on which
`NK.HassePrinciple.locUnits` is defined (`unitsTransport`).

The transport is *definite* (built from `groupCohomology.mapIso`, hence from maps on cochains), so
statements whose hypotheses are routed through it are usable in proofs — unlike a transport built
from `Classical.choice` on a `Nonempty`.
-/

open CategoryTheory

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u

namespace NK.NUV2.LC

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The level dictionary** at a level `L` for the full absolute Galois group:
`LevelGroup ⊤ L = Gal(K'/K)/Gal(K'/L) ≃* Gal(L/K)`, given by restriction. -/
noncomputable def levelGroupEquivTop (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L ≃* Gal(↥L.toIntermediateField/K) := by
  classical
  have hsurj : Function.Surjective
      (NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L) := by
    intro y
    obtain ⟨x, hx⟩ := AlgEquiv.restrictNormalHom_surjective (F := K)
      (K₁ := ↥L.toIntermediateField) (E := K') y
    refine ⟨QuotientGroup.mk (⟨x, Subgroup.mem_top x⟩ : ↥(⊤ : Subgroup Gal(K'/K))), ?_⟩
    rw [NK.HassePrinciple.levelGroupRestrictHom_mk]
    exact hx
  have hinj : Function.Injective
      (NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L) := by
    intro a b hab
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective
      (L.fixingSubgroup.subgroupOf (⊤ : Subgroup Gal(K'/K))) a
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective
      (L.fixingSubgroup.subgroupOf (⊤ : Subgroup Gal(K'/K))) b
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at *
    rw [NK.HassePrinciple.levelGroupRestrictHom_mk,
      NK.HassePrinciple.levelGroupRestrictHom_mk] at hab
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    have h1 : NK.HassePrinciple.levelRestrict L
        (↑((u : ↥(⊤ : Subgroup Gal(K'/K))) / v) : Gal(K'/K)) = 1 := by
      rw [Subgroup.coe_div, map_div, hab]
      simp
    have h2 : (⟨↑((u : ↥(⊤ : Subgroup Gal(K'/K))) / v), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup Gal(K'/K))) ∈
        (NK.HassePrinciple.levelRestrictHom (⊤ : Subgroup Gal(K'/K)) L).ker := by
      rw [MonoidHom.mem_ker]
      simpa using h1
    rw [NK.HassePrinciple.levelRestrictHom_ker] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  exact MulEquiv.ofBijective _ ⟨hinj, hsurj⟩

/-- The computation rule for the level dictionary: it is the restriction map. -/
theorem levelGroupEquivTop_apply (L : FiniteGaloisIntermediateField K K')
    (x : NK.BrauerHasse.LevelGroup (⊤ : Subgroup Gal(K'/K)) L) :
    levelGroupEquivTop (K := K) (K' := K') L x =
      NK.HassePrinciple.levelGroupRestrictHom (⊤ : Subgroup Gal(K'/K)) L x :=
  MulEquiv.ofBijective_apply _ _ x

/-- **The units transport**: the level cohomology `H²(LevelGroup ⊤ L, Lˣ)` is the group cohomology
`H²(Gal(L/K), Lˣ)` in which `NK.HassePrinciple.locUnits` is stated. -/
noncomputable def unitsTransport (L : FiniteGaloisIntermediateField K K') :
    (NK.HassePrinciple.UnitsLevelH2 (K := K) (K' := K') (⊤ : Subgroup Gal(K'/K)) L) ≃+
      (groupCohomology (NK.HassePrinciple.unitsRep K ↥L) 2) := by
  refine ((groupCohomology.mapIso (A := NK.HassePrinciple.unitsRep K ↥L)
    (B := NK.HassePrinciple.unitsLevelRep (⊤ : Subgroup Gal(K'/K)) L)
    (levelGroupEquivTop (K := K) (K' := K') L)
    (LinearEquiv.refl NK.HassePrinciple.CoeffInt (Additive (↥L.toIntermediateField)ˣ)) ?_ 2).toLinearEquiv).toAddEquiv
  intro g
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.refl_apply]
  rfl

end NK.NUV2.LC
