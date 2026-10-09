import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.archPhiP2
import Submission.Work.SSGRoute.ArchDictionary.extOneDictNaturalH1
import Submission.Work.SSGRoute.ArchDictionary.p2Link
import Submission.Work.SSGRoute.ArchDictionary.archAcH1Natural
import Submission.Work.SSGRoute.ArchDictionary.placeLocalFieldComplex
import Submission.Work.SSGRoute.E1aClean.globalDictionaryCanonDefs
import Submission.Work.SSGRoute.ArchDictionary.archSeamDefs
import Submission.Work.SSGRoute.ArchDictionary.postcompUnitsBijective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead design archp2_1008. READ Submission/_lead_design/archp2_1008/ARCHP2_PLAN.md (and .lean). The old localCoeffP2/archPhiDef route can NEVER satisfy the comparison square: see the D₄ model in ARCHP2_model.lean (decide). This route uses Φ := ArchSeamP2.archPhiOf and Ψ := seamCoeffLoc (the seam-push of e1aCoeffNat), from the installed module Submission.Work.SSGRoute.ArchDictionary.archSeamDefs. The statement is lead-checked and elaborates. Copy any helper you need from the plan .lean; do not import _lead_design. No native_decide; never write maxHeartbeats 0.
-/

/-!
# Bijectivity of the seam-pushed local coefficient identification `seamCoeffLoc`

`ArchSeamP2.seamCoeffLoc` is, by definition, the composite

  `E --e1aCoeffNat--> (E'.V →+ Ωˣ) --postcompose seamUnits--> (E'.V →+ K_wˣ) --linAddEquiv.symm--> (E'.V →ₗ K_wˣ)`

Each of the three factors is a bijection:

* `ExtChain.e1aCoeffNat` is an additive equivalence (`AddEquiv`);
* `linAddEquiv` is the (additive) identification of `Coeff`-linear and additive maps
  (`Coeff = ULift ℤ`), an `AddEquiv`;
* the middle factor, postcomposition with `seamUnits : Ωˣ →* K_wˣ`, is a bijection
  (`Work.SSGRoute.ArchDictionary.postcompUnitsBijective`, proved in the sibling module
  `ArchDictionary/postcompUnitsBijective.lean`) because `E'.V = DualMod 2 (E ⊗ T)` is `2`-torsion
  (a `ZMod 2`-module), hence every additive map out of it takes values in the `2`-torsion
  `μ₂ = {1, -1}` of the target, and `seamUnits` restricts to a bijection `μ₂(Ω) → μ₂(K_w)` (it
  maps `1 ↦ 1` and `-1 ↦ -1`).

The two facts about `seamUnits` needed for that lemma are `seamUnits_inj_aux` and
`seamUnits_neg_one_aux` below.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt Work.SSGRoute.ArchDictionary
  Work.SSGRoute.ArchDictionary.ArchSeamP2
open scoped TensorProduct

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-! ## Two facts about `seamUnits` -/

/-- `seamUnits` is injective: it is `Units.map` of the injective ring hom `e.symm ∘ φ`. -/
private theorem seamUnits_inj_aux (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥) :
    Function.Injective (seamUnits c hc2 hc1 φ hlink w hw hne) := by
  show Function.Injective (Units.map ((Classical.choose
    (unitsToLocalUnitsHom_eq_embedding 2 k Ω K c hc2 hc1 φ hlink w hw hne)).symm.toRingHom.comp
      φ).toMonoidHom)
  apply Units.map_injective
  exact RingHom.injective _

/-- `seamUnits` sends `-1` to `-1`. -/
private theorem seamUnits_neg_one_aux (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥) :
    seamUnits c hc2 hc1 φ hlink w hw hne (-1) = -1 := by
  show Units.map ((Classical.choose
    (unitsToLocalUnitsHom_eq_embedding 2 k Ω K c hc2 hc1 φ hlink w hw hne)).symm.toRingHom.comp
      φ).toMonoidHom (-1) = -1
  apply Units.ext
  rw [Units.coe_map]
  simp only [Units.val_neg, Units.val_one]
  change ((Classical.choose
    (unitsToLocalUnitsHom_eq_embedding 2 k Ω K c hc2 hc1 φ hlink w hw hne)).symm.toRingHom.comp
      φ) (-1 : Ω) = -1
  rw [map_neg, map_one]

/-! ## The main theorem -/

theorem seamCoeffLoc_bijective {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
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
    Function.Bijective
      (seamCoeffLoc T hζ hζK hT c hc2 hc1 φ hlink w hw hne E) := by
  -- `E'.V = DualMod 2 (E ⊗ T)` is `2`-torsion.
  have hV2 : ∀ v : Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T), (2 : ℕ) • v = 0 := by
    intro v
    have hv : v + v = 0 := by
      rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from by decide, zero_smul]
    rw [two_nsmul]
    exact hv
  have hnegne : (-1 : (NK.GlobalCFT.Place.localField ↥K w)ˣ) ≠ 1 := by
    intro h
    apply localField_two_ne_zero (K := K) w
    have h' : (-1 : NK.GlobalCFT.Place.localField ↥K w) = 1 := by
      simpa using congrArg
        (fun u : (NK.GlobalCFT.Place.localField ↥K w)ˣ =>
          (u : NK.GlobalCFT.Place.localField ↥K w)) h
    have h3 : (-1 : NK.GlobalCFT.Place.localField ↥K w) - 1 = 0 := by rw [h', sub_self]
    have h2 : (2 : NK.GlobalCFT.Place.localField ↥K w) = 0 := by
      rw [show (2 : NK.GlobalCFT.Place.localField ↥K w) =
        -((-1 : NK.GlobalCFT.Place.localField ↥K w) - 1) by ring, h3, neg_zero]
    exact h2
  -- the middle factor: postcomposition with `seamUnits`
  have hpost : Function.Bijective
      (fun g : Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T) →+ Additive Ωˣ =>
        (MonoidHom.toAdditive (seamUnits c hc2 hc1 φ hlink w hw hne)).comp g) :=
    postcompUnitsBijective (seamUnits c hc2 hc1 φ hlink w hw hne)
      (seamUnits_inj_aux c hc2 hc1 φ hlink w hw hne)
      (seamUnits_neg_one_aux c hc2 hc1 φ hlink w hw hne) hnegne hV2
  -- the outer factor: `linAddEquiv.symm`
  have hF : Function.Bijective
      (⇑((Work.SSGRoute.linAddEquiv
        (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))
        (Additive (NK.GlobalCFT.Place.localField ↥K w)ˣ)).symm)) :=
    (Work.SSGRoute.linAddEquiv
      (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))
      (Additive (NK.GlobalCFT.Place.localField ↥K w)ˣ)).symm.bijective
  -- the inner factor: `e1aCoeffNat`
  have he1 : Function.Bijective
      (⇑(Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E).toAddMonoidHom) :=
    (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E).bijective
  exact hF.comp (hpost.comp he1)

end Work.SSGRoute.ArchDictionary
