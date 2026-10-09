import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.archCoeffP2
import Submission.Work.SSGRoute.ArchDictionary.p2Link
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Equivariance of the local coefficient identification at `p = 2`

`ArchDictionary.localCoeffP2` is the coefficient identification
`E ≃+ Hom_ℤ(E', K_wˣ)`, `E' = DualMod 2 (E ⊗ T)`, `e ↦ (φ ↦ (-1) ^ (φ (e ⊗ t₀)))`, which is the
archimedean local E1c datum at `p = 2`.  For `mapH1 (localCoeffP2)⁻¹` to typecheck one needs the
**equivariance** of this map for the `D_w`-action (the conjugation action on `Hom_ℤ(E', K_wˣ)`
against the Galois action on `E`), which is what this file proves.

The mathematical content is entirely elementary:

* at `p = 2` the cyclotomic dual `T` is a *trivial* `Gal(K/k)`-module
  (`cyclotomicDual_trivial_p2`), so `σ • (e ⊗ t₀) = (σ • e) ⊗ t₀`;
* the `D_w`-action on `K_wˣ` is induced by the *ring* automorphism `localAutHom w σ` of the local
  field, hence fixes `-1`, so it fixes every element of `μ₂ = {±1}` (`localUnitsEquiv_neg_one`,
  `zetaPowHom_fix_localUnits`).

Given those, both sides of the equivariance identity compute to `(-1) ^ (φ ((σ • e) ⊗ t₀))`.
-/

namespace Work.SSGRoute.ArchDictionary

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- The `D_w`-action on the local units fixes `-1` (it is induced by a ring automorphism of the
local field). -/
theorem localUnitsEquiv_neg_one (w : NK.GlobalCFT.Place ↥K)
    (d : ↥(SSGRoute.PTExt.decompK (k := k) w)) :
    NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K) w d
      (-1 : (NK.GlobalCFT.Place.localField ↥K w)ˣ) = -1 := by
  apply Units.ext
  rw [NK.HassePrinciple.coe_localUnitsEquiv]
  simp

/-- The `D_w`-action on `K_wˣ` fixes every element of the group `μ₂` of square roots of unity. -/
theorem zetaPowHom_fix_localUnits (w : NK.GlobalCFT.Place ↥K)
    (d : ↥(SSGRoute.PTExt.decompK (k := k) w)) (y : ZMod 2) :
    (SSGRoute.PTExt.localUnitsK (k := k) w).ρ d
        (Work.SSGRoute.zetaPowHom (-1 : (NK.GlobalCFT.Place.localField ↥K w)ˣ)
          (neg_one_isPrimitiveRoot_units (localField_two_ne_zero (K := K) w)) y)
      = Work.SSGRoute.zetaPowHom (-1 : (NK.GlobalCFT.Place.localField ↥K w)ˣ)
          (neg_one_isPrimitiveRoot_units (localField_two_ne_zero (K := K) w)) y := by
  have hρ : ∀ (d : ↥(SSGRoute.PTExt.decompK (k := k) w))
      (u : (NK.GlobalCFT.Place.localField ↥K w)ˣ),
      (SSGRoute.PTExt.localUnitsK (k := k) w).ρ d (Additive.ofMul u)
        = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K) w d u) :=
    fun _ _ => rfl
  have hlu := localUnitsEquiv_neg_one (k := k) (K := K) w
  obtain ⟨n, hn⟩ : ∃ n : ℕ, y = (n : ZMod 2) := ⟨y.val, (ZMod.natCast_zmod_val y).symm⟩
  subst hn
  rw [Work.SSGRoute.zetaPowHom_coe_nat]
  exact (hρ d (((-1 : (NK.GlobalCFT.Place.localField ↥K w)ˣ)) ^ n)).trans
    (congrArg Additive.ofMul (by rw [map_pow, hlu d]))

/-- At `p = 2` the cyclotomic dual `T` is a trivial `Gal(K/k)`-module. -/
theorem cyclotomicDual_trivial_p2 (T : Type) [AddCommGroup T] [Module (ZMod 2) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω)) :
    ∀ (τ : K ≃ₐ[k] K) (t : T), τ • t = t := by
  intro τ t
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) Ω τ
  have hc : σ • (-1 : Ω) = (-1 : Ω) ^ 1 := by
    rw [pow_one]
    show σ (-1) = -1
    simp
  have h := hT.2 σ 1 hc t
  rw [one_smul, hσ] at h
  exact h

theorem localCoeffP2IsEquivariant (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (T : Type) [AddCommGroup T] [Module (ZMod 2) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (w : NK.GlobalCFT.Place ↥K) (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E] :
    @Work.GroupCohomology.IsEquivariant ↥(SSGRoute.PTExt.decompK w)
      ((Work.SSGRoute.ArchDictionary.Eprime 2 k Ω K T E).V →ₗ[SSGRoute.PTExt.Coeff]
        (SSGRoute.PTExt.localUnitsK w).V) E _ _ _
      (Work.SSGRoute.homRepDistribMulAction
        (Rep.res (SSGRoute.PTExt.decompK w).subtype
          (Work.SSGRoute.ArchDictionary.Eprime 2 k Ω K T E))
        (SSGRoute.PTExt.localUnitsK w))
      (Work.SSGRoute.ArchDictionary.dcAct K E w)
      ((Work.SSGRoute.ArchDictionary.localCoeffP2 T hT E w).symm.toAddMonoidHom) := by
  letI hE : DistribMulAction ↥(SSGRoute.PTExt.decompK (k := k) w) E := dcAct K E w
  letI hX : DistribMulAction ↥(SSGRoute.PTExt.decompK (k := k) w)
      ((Eprime 2 k Ω K T E).V →ₗ[SSGRoute.PTExt.Coeff]
        (SSGRoute.PTExt.localUnitsK (k := k) w).V) :=
    Work.SSGRoute.homRepDistribMulAction
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
      (SSGRoute.PTExt.localUnitsK (k := k) w)
  have hTtriv := cyclotomicDual_trivial_p2 (k := k) (Ω := Ω) (K := K) T hT
  intro g x
  have key : ∀ e : E,
      localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w (g • e)
        = g • localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w e := by
    intro e
    apply LinearMap.ext
    intro φ
    rw [show (g • localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w e) φ
        = (SSGRoute.PTExt.localUnitsK (k := k) w).ρ g
            ((localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w e)
              ((Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
                (Eprime 2 k Ω K T E)).ρ g⁻¹ φ)) from rfl]
    rw [localCoeffP2_apply (k := k) (Ω := Ω) (K := K) T hT E w (g • e) φ,
        localCoeffP2_apply (k := k) (Ω := Ω) (K := K) T hT E w e
          ((Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (Eprime 2 k Ω K T E)).ρ g⁻¹ φ)]
    have hψ : ((Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (Eprime 2 k Ω K T E)).ρ g⁻¹) φ
        = (Eprime 2 k Ω K T E).ρ ((g : K ≃ₐ[k] K)⁻¹) φ := rfl
    rw [hψ, show (Eprime 2 k Ω K T E).ρ ((g : K ≃ₐ[k] K)⁻¹) φ
        = (((g : K ≃ₐ[k] K)⁻¹)
            • (show Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T) from φ)) from rfl,
      Work.SSGRoute.DualMod.dualSMul_apply, inv_inv]
    have hsmulE : (g • e : E) = (g : K ≃ₐ[k] K) • e := rfl
    have hAB : (g : K ≃ₐ[k] K) • (e ⊗ₜ[ZMod 2] Work.SSGRoute.PT.e1aTGen 2 T hT.1)
        = (g • e) ⊗ₜ[ZMod 2] Work.SSGRoute.PT.e1aTGen 2 T hT.1 := by
      rw [Work.Shrinking.diagTensor_smul_tmul,
        hTtriv (g : K ≃ₐ[k] K) (Work.SSGRoute.PT.e1aTGen 2 T hT.1), ← hsmulE]
    rw [hAB]
    exact (zetaPowHom_fix_localUnits (k := k) (K := K) w g
      ((show Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T) from φ)
        ((g • e) ⊗ₜ[ZMod 2] Work.SSGRoute.PT.e1aTGen 2 T hT.1))).symm
  have hx : (g • x : (Eprime 2 k Ω K T E).V →ₗ[SSGRoute.PTExt.Coeff]
        (SSGRoute.PTExt.localUnitsK (k := k) w).V)
      = Work.SSGRoute.homSMul
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) g x := rfl
  have step1 : (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm (g • x)
      = (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm
          (Work.SSGRoute.homSMul
            (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
            (SSGRoute.PTExt.localUnitsK (k := k) w) g x) :=
    congrArg (fun y => (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm y) hx
  have hB : (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm
        (Work.SSGRoute.homSMul
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) g x)
      = (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm
          (Work.SSGRoute.homSMul
            (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
            (SSGRoute.PTExt.localUnitsK (k := k) w) g
            ((localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w)
              ((localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm x))) :=
    (congrArg (fun y => (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm
        (Work.SSGRoute.homSMul
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) g y))
      (AddEquiv.apply_symm_apply (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w) x)).symm
  have hA : (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm
        (Work.SSGRoute.homSMul
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) g
          ((localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w)
            ((localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm x)))
      = (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm
          ((localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w)
            (g • (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm x)) :=
    congrArg (fun y => (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm y)
      (key ((localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm x)).symm
  have hC : (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm
        ((localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w)
          (g • (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm x))
      = g • (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm x :=
    AddEquiv.symm_apply_apply (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w)
      (g • (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w).symm x)
  exact step1.trans (hB.trans (hA.trans hC))

end Work.SSGRoute.ArchDictionary
