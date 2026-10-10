import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.archPhiSeam_square2
import Submission.Work.SSGRoute.ArchDictionary.seamCoeffLoc_bijective
import Submission.Work.SSGRoute.ArchDictionary.seamCoeffLoc_isEquivariant
import Submission.Work.SSGRoute.ArchDictionary.seamCoeffLoc_natural
import Submission.Work.SSGRoute.E1aClean.LeadNatWit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead design archp2_1008. READ Submission/_lead_design/archp2_1008/ARCHP2_PLAN.md (and .lean). The old localCoeffP2/archPhiDef route can NEVER satisfy the comparison square: see the D₄ model in ARCHP2_model.lean (decide). This route uses Φ := ArchSeamP2.archPhiOf and Ψ := seamCoeffLoc (the seam-push of e1aCoeffNat), from the installed module Submission.Work.SSGRoute.ArchDictionary.archSeamDefs. The statement is lead-checked and elaborates. Copy any helper you need from the plan .lean; do not import _lead_design. No native_decide; never write maxHeartbeats 0.

## Assembly (lead design `archp2_1008` §H)

`ζ = −1` (`IsPrimitiveRoot.eq_neg_one_of_two_right`), then `ArchPlaceDict` is supplied by the
`E`-indexed family `Φ E := archPhiOf … (seamCoeffLoc E) (seamCoeffLoc_bijective E)
(seamCoeffLoc_isEquivariant E)`; its two clauses are `archPhiSeam_square` (the comparison square,
with `Ψ` pinned pointwise to `seamCoeffLoc` by `rfl`) and `archPhiOf_natural` (naturality, with the
pointwise hypothesis `seamCoeffLoc_natural`). -/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt
open Work.SSGRoute.ArchDictionary.ArchSeamP2

theorem archPlaceDict_of_nonsplit_p2
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    Work.SSGRoute.LeadNatWit.ArchPlaceDict 2 k Ω K ζ hζ hζK T hT c w := by
  obtain rfl : ζ = -1 := hζ.eq_neg_one_of_two_right
  let Ψ := fun (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E] =>
    AddEquiv.ofBijective (seamCoeffLoc T hζ hζK hT c hc2 hc1 φ hlink w hw hne E)
      (seamCoeffLoc_bijective T hζ hζK hT c hc2 hc1 φ hlink w hw hne E)
  have hΦ := fun (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E] =>
    seamCoeffLoc_isEquivariant T hζ hζK hT c hc2 hc1 φ hlink w hw hne E
  refine ⟨fun E _ _ _ _ _ => archPhiOf c hc2 hc1 φ hlink w hw hne E
      (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)) (Ψ E) (by exact hΦ E)
      (@isEquivariant_symm ↥(decompK (k := k) w) E
        ((Eprime 2 k Ω K T E).V →ₗ[Coeff] (localUnitsK (k := k) w).V) _ _ _ (dcAct K E w)
        (Work.SSGRoute.homRepDistribMulAction
          (Rep.res (decompK (k := k) w).subtype (Eprime 2 k Ω K T E)) (localUnitsK (k := k) w))
        (Ψ E) (hΦ E)), ?_, ?_⟩
  · intro E _ _ _ _ _ b hb hl
    exact archPhiSeam_square2 T hζ hζK hT c hc2 hc1 φ hlink w hw hne E (Ψ E) (fun e => rfl)
      (by exact hΦ E) _ b hb hl
  · intro E _ _ _ _ _ E₂ _ _ _ _ _ f hf F' hF' x
    exact archPhiOf_natural T c hc2 hc1 φ hlink w hw hne E E₂ (Ψ E) (by exact hΦ E) _ (Ψ E₂)
      (by exact hΦ E₂) _ f hf F' (fun e m => congrFun (seamCoeffLoc_natural T hζ hζK hT c hc2 hc1
        φ hlink w hw hne E E₂ f hf F' hF' e) m) x

end Work.SSGRoute.ArchDictionary
