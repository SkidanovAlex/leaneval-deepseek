import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.ArchDictionary.archSeamDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead design archp2_1008. READ Submission/_lead_design/archp2_1008/ARCHP2_PLAN.md (and .lean). The old localCoeffP2/archPhiDef route can NEVER satisfy the comparison square: see the D₄ model in ARCHP2_model.lean (decide). This route uses Φ := ArchSeamP2.archPhiOf and Ψ := seamCoeffLoc (the seam-push of e1aCoeffNat), from the installed module Submission.Work.SSGRoute.ArchDictionary.archSeamDefs. The statement is lead-checked and elaborates. Copy any helper you need from the plan .lean; do not import _lead_design. No native_decide; never write maxHeartbeats 0.
-/

/-! ## Proof strategy (the seam is only ever evaluated on `2`-torsion units)

`seamUnits` is built from `Classical.choose (unitsToLocalUnitsHom_eq_embedding ...)`, whose
*only* available property is `seamUnits_on_K` (its values on `Kˣ`); the chosen spelling
`K_w ≃+* ℂ` is opaque, so no equivariance of `seamUnits` on all of `Ωˣ` may be used.

This is not an obstacle here: `e1aCoeffNat e : E' →+ Ωˣ` is a homomorphism out of the
`ZMod 2`-module `E' = DualMod 2 (E ⊗ T)`, hence its values are `2`-torsion, hence `= ±1`, and
`±1 ∈ K` by `hζK`.  So the equivariance of `seamCoeffLoc` reduces to its values on `μ₂ ⊆ K`,
where it is forced by `seamUnits_on_K` and `localAut_algebraMap`:
`seamUnits (c • v) = localUnitsEquiv w d (seamUnits v)` for `v = ±1` and `d = res k K c`.

`D_w = ⟨res k K c⟩` (`PT.decompK_linked`) is a group of exponent `2`, so every `d ∈ D_w` is `1`
or `res k K c`, and the two cases are handled separately. -/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt Work.SSGRoute.ArchDictionary
  Work.SSGRoute.ArchDictionary.ArchSeamP2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

section Helpers

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- In a group, an element of `⟨r⟩` where `r * r = 1` is `1` or `r`. -/
lemma eq_one_or_eq_of_mem_zpowers_of_mul_self_eq_one {G : Type*} [Group G] {r x : G}
    (hr : r * r = 1) (hx : x ∈ Subgroup.zpowers r) : x = 1 ∨ x = r := by
  let H : Subgroup G :=
    { carrier := ({1, r} : Set G)
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [hr]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl
        · left; simp
        · right; exact inv_eq_of_mul_eq_one_right hr }
  have hrH : r ∈ H := by
    change r ∈ ({1, r} : Set G); right; rfl
  have hxH : x ∈ H := (Subgroup.zpowers_le.mpr hrH) hx
  have hxH' : x ∈ ({1, r} : Set G) := hxH
  simpa using hxH'

/-- The local decomposition action on the local units is compatible with the canonical embedding
`Kˣ → K_wˣ`: `localUnitsEquiv w d (unitsToLocalUnitsHom w x) = unitsToLocalUnitsHom w (d • x)`. -/
lemma localUnitsEquiv_unitsToLocalUnitsHom
    (w : NK.GlobalCFT.Place ↥K) (d : ↥(decompK (k := k) w)) (x : (↥K)ˣ) :
    NK.HassePrinciple.localUnitsEquiv (K := k) w d (NK.HassePrinciple.unitsToLocalUnitsHom w x)
      = NK.HassePrinciple.unitsToLocalUnitsHom w
          (Units.map (((d : ↥K ≃ₐ[k] ↥K) : ↥K →+* ↥K).toMonoidWithZeroHom) x) := by
  apply Units.ext
  simp only [NK.HassePrinciple.coe_localUnitsEquiv, NK.HassePrinciple.unitsToLocalUnitsHom,
    Units.coe_map]
  exact NK.HassePrinciple.localAut_algebraMap (K := k) (L := ↥K) w d (x : ↥K)

/-- The seam on units is equivariant at the element `-1` (which lies in `K` by `hζK`). -/
lemma seamUnits_neg_one_equivariant
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥) (hζK : (-1 : Ω) ∈ K) (d : ↥(decompK (k := k) w))
    (hd : (d : K ≃ₐ[k] K) = SSGRoute.res k K c) :
    seamUnits c hc2 hc1 φ hlink w hw hne
        (Work.SSGRoute.algEquivUnitsMapΩ k Ω c
          (Units.map (algebraMap ↥K Ω).toMonoidHom (-1 : (↥K)ˣ)))
      = NK.HassePrinciple.localUnitsEquiv (K := k) w d
          (seamUnits c hc2 hc1 φ hlink w hw hne
            (Units.map (algebraMap ↥K Ω).toMonoidHom (-1 : (↥K)ˣ))) := by
  have harg : Work.SSGRoute.algEquivUnitsMapΩ k Ω c
        (Units.map (algebraMap ↥K Ω).toMonoidHom (-1 : (↥K)ˣ))
      = Units.map (algebraMap ↥K Ω).toMonoidHom (-1 : (↥K)ˣ) := by
    apply Units.ext
    simp only [Work.SSGRoute.algEquivUnitsMapΩ_coe, Units.coe_map]
    simp
  rw [harg]
  rw [seamUnits_on_K c hc2 hc1 φ hlink w hw hne (-1 : (↥K)ˣ)]
  rw [localUnitsEquiv_unitsToLocalUnitsHom]
  congr 1
  apply Units.ext
  simp only [Units.coe_map]
  simp

/-- **The seam is equivariant on `2`-torsion units.**  If `u ∈ Ωˣ` is `2`-torsion then it is `±1`,
and for both of these the seam intertwines the action of `c` on `Ωˣ` with the local action of
`d = res k K c` on `K_wˣ`. -/
lemma seamUnits_smul_eq_of_two_nsmul_eq_zero
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥) (hζK : (-1 : Ω) ∈ K) (d : ↥(decompK (k := k) w))
    (hd : (d : K ≃ₐ[k] K) = SSGRoute.res k K c) (u : Additive Ωˣ)
    (hu : (2 : ℕ) • u = 0) :
    seamUnits c hc2 hc1 φ hlink w hw hne (Additive.toMul (c • u))
      = NK.HassePrinciple.localUnitsEquiv (K := k) w d
          (seamUnits c hc2 hc1 φ hlink w hw hne (Additive.toMul u)) := by
  have hv2 : Additive.toMul u * Additive.toMul u = 1 := by
    have h := congrArg Additive.toMul hu
    rw [toMul_nsmul, toMul_zero, pow_two] at h
    exact h
  have hv2' : ((Additive.toMul u : Ωˣ) : Ω) ^ 2 = 1 := by
    rw [pow_two, ← Units.val_mul, hv2, Units.val_one]
  rcases sq_eq_one_iff.mp hv2' with hv1 | hvm1
  · have hv : Additive.toMul u = 1 := Units.ext hv1
    have hu0 : u = 0 := by
      rw [← ofMul_toMul u, hv, ofMul_one]
    rw [hu0, smul_zero, toMul_zero]
    simp
  · have hv : Additive.toMul u = Units.map (algebraMap ↥K Ω).toMonoidHom (-1 : (↥K)ˣ) := by
      apply Units.ext
      rw [hvm1, Units.coe_map]
      simp
    have hu' : u = Additive.ofMul (Units.map (algebraMap ↥K Ω).toMonoidHom (-1 : (↥K)ˣ)) := by
      rw [← ofMul_toMul u, hv]
    rw [hu', Work.SSGRoute.addUnits_smul_toMulΩ, toMul_ofMul]
    exact seamUnits_neg_one_equivariant c hc2 hc1 φ hlink w hw hne hζK d hd

end Helpers

theorem seamCoeffLoc_isEquivariant {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hζ : IsPrimitiveRoot (-1 : Ω) 2) (hζK : (-1 : Ω) ∈ K)
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E] :
    @Work.GroupCohomology.IsEquivariant ↥(decompK (k := k) w) E
      ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) w).V) _ _ _
      (dcAct K E w)
      (Work.SSGRoute.homRepDistribMulAction
        (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) w))
      (seamCoeffLoc T hζ hζK hT c hc2 hc1 φ hlink w hw hne E) := by
  intro d e
  have hD : decompK (k := k) w = Subgroup.zpowers (SSGRoute.res k K c) := by
    rw [hw]
    rw [Work.SSGRoute.PT.decompK_linked k Ω K c hc2 hc1 φ hlink]
    exact MonoidHom.map_zpowers (SSGRoute.res k K) c
  have hr2 : SSGRoute.res k K c * SSGRoute.res k K c = 1 := by
    have h := map_mul (SSGRoute.res k K) c c
    rw [show c * c = 1 by simpa [pow_two] using hc2, map_one] at h
    exact h.symm
  have hcases : (d : K ≃ₐ[k] K) = 1 ∨ (d : K ≃ₐ[k] K) = SSGRoute.res k K c := by
    have hmem : (d : K ≃ₐ[k] K) ∈ Subgroup.zpowers (SSGRoute.res k K c) := by
      rw [← hD]; exact d.2
    exact eq_one_or_eq_of_mem_zpowers_of_mul_self_eq_one hr2 hmem
  rcases hcases with h1 | hres
  · have hd1 : d = 1 := Subtype.ext h1
    rw [hd1]
    simp
  · have hd : (d : K ≃ₐ[k] K) = SSGRoute.res k K c := hres
    ext x
    change Additive.ofMul ((seamUnits c hc2 hc1 φ hlink w hw hne)
        (Additive.toMul ((Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E
          (d • e)) x)))
      = ((localUnitsK (k := k) w).ρ d)
          (Additive.ofMul ((seamUnits c hc2 hc1 φ hlink w hw hne)
            (Additive.toMul ((Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E e)
              ((Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)).ρ d⁻¹ x)))))
    have hde : d • e = (SSGRoute.res k K c) • e := by
      change (d : K ≃ₐ[k] K) • e = (SSGRoute.res k K c) • e
      rw [hd]
    have hΛeq : Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E (d • e)
        = c • (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E e) := by
      rw [hde]
      exact Work.SSGRoute.ExtChain.e1aCoeffNat_equivariant 2 k Ω K (-1) hζ hζK T hT E c e
    rw [hΛeq, Work.SSGRoute.homCoind.smul_apply]
    have hargR : (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)).ρ d⁻¹ x
        = (Eprime 2 k Ω K T E).ρ ((SSGRoute.res k K c)⁻¹) x := by
      show (Eprime 2 k Ω K T E).ρ ((decompK (k := k) w).subtype d⁻¹) x = _
      rw [map_inv]
      exact congrArg (fun γ : K ≃ₐ[k] K => ((Eprime 2 k Ω K T E).ρ γ⁻¹) x) hd
    rw [hargR]
    have hN : ((localUnitsK (k := k) w).ρ d)
        (Additive.ofMul ((seamUnits c hc2 hc1 φ hlink w hw hne)
          (Additive.toMul ((Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E e)
            ((Eprime 2 k Ω K T E).ρ ((SSGRoute.res k K c)⁻¹) x)))))
        = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) w d
            ((seamUnits c hc2 hc1 φ hlink w hw hne)
              (Additive.toMul ((Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E e)
                ((Eprime 2 k Ω K T E).ρ ((SSGRoute.res k K c)⁻¹) x))))) := rfl
    rw [hN]
    have hm : (2 : ℕ) • ((Eprime 2 k Ω K T E).ρ ((SSGRoute.res k K c)⁻¹) x) = 0 := by
      haveI : Module (ZMod 2) ↑(Eprime 2 k Ω K T E) :=
        inferInstanceAs (Module (ZMod 2) (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T)))
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 ((Eprime 2 k Ω K T E).ρ ((SSGRoute.res k K c)⁻¹) x),
        ZMod.natCast_self 2, zero_smul]
    have hu2 : (2 : ℕ) • ((Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E e)
        ((Eprime 2 k Ω K T E).ρ ((SSGRoute.res k K c)⁻¹) x)) = 0 := by
      rw [← map_nsmul, hm, map_zero]
    exact congrArg Additive.ofMul
      (seamUnits_smul_eq_of_two_nsmul_eq_zero c hc2 hc1 φ hlink w hw hne hζK d hd _ hu2)

end Work.SSGRoute.ArchDictionary
