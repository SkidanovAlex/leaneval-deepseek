import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
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

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt Work.SSGRoute.ArchDictionary
  Work.SSGRoute.ArchDictionary.ArchSeamP2

/-- **Computation rule for `seamCoeffLoc`**: the seam-push of `e1aCoeffNat` applied to a
coefficient `e` and evaluated at `m` is `seamUnits (e1aCoeffNat e m)`.

This is `rfl`: `seamCoeffLoc` is `seamUnits ∘ e1aCoeffNat` pushed through the (definitional)
identification `Hom_ℤ(-,K_wˣ) ≃ (K_wˣ)^(-)` of `Work.SSGRoute.linAddEquiv`. -/
theorem seamCoeffLoc_apply {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
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
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (e : E) (m : Eprime 2 k Ω K T E) :
    (seamCoeffLoc T hζ hζK hT c hc2 hc1 φ hlink w hw hne E e) m
      = seamUnits c hc2 hc1 φ hlink w hw hne
          (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E e m) := rfl

theorem seamCoeffLoc_natural {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
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
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod 2) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E₂] [Finite E₂]
    (f : E →ₗ[ZMod 2] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    (F' : Eprime 2 k Ω K T E₂ ⟶ Eprime 2 k Ω K T E)
    (hF' : ∀ (ψ : Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E₂ T)) (e : E) (t : T),
      (show Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T) from F'.hom ψ)
        (TensorProduct.tmul (ZMod 2) e t) = ψ (TensorProduct.tmul (ZMod 2) (f e) t))
    (e : E) :
    ⇑(seamCoeffLoc T hζ hζK hT c hc2 hc1 φ hlink w hw hne E₂ (f e))
      = fun m => (seamCoeffLoc T hζ hζK hT c hc2 hc1 φ hlink w hw hne E e) (F'.hom m) := by
  funext m
  rw [seamCoeffLoc_apply T hζ hζK hT c hc2 hc1 φ hlink w hw hne E₂ (f e) m,
    seamCoeffLoc_apply T hζ hζK hT c hc2 hc1 φ hlink w hw hne E e (F'.hom m),
    Work.SSGRoute.ExtChain.e1aCoeffNat_natural_aux 2 k Ω K (-1) hζ hζK T hT E E₂ f hf F' hF' e]
  rfl

end Work.SSGRoute.ArchDictionary
