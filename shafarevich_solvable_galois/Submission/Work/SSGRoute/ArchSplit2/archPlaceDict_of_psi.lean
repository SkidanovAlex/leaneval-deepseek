import Mathlib
import Submission.Work.SSGRoute.ArchSplit2.splitPlace_family_clause
import Submission.Work.SSGRoute.ArchSplit2.uniformSquare_of_family_clause
import Submission.Work.SSGRoute.ArchNat.archUniformNatural
import Submission.Work.SSGRoute.ArchDictionary_aux.SettingLemmas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The split-place (`decompK w = ⊥`) branch of `ArchPlaceDict`

`ArchPlaceDict p k Ω K ζ hζ hζK T hT c w` (the lead's `_lead_design/ssg_natwit_0820.lean`, §(c) ARCH)
is the `E`-indexed `Φ : Ac c E ≃+ Ext¹_{D_w}(E'|, K_wˣ)` with the comparison square against
`globalDictionaryCanon` and naturality in the coefficient — verbatim the `hsq` input of the proved
`ArchNat.archimedeanDictUniformNat`, and the archimedean half of the leaf
`E1aClean.localDictionary_natural_family_arch`.

This file assembles that dictionary at a **split** place (`decompK w = ⊥`, real place, `p = 2`) from
the canonical split dictionary `ψ` of `ArchSplit2.archSplit2_canonical` (A3 of
`_lead_design/ssg_arch2_2320.md`), via

* `ArchSplit2.splitPlace_family_clause` (the `βc`-family with the five family clauses), and
* `ArchSplit2.uniformSquare_of_family_clause` (from `βc` to `Φ`, square + naturality on
  representatives).

The only new content here is the last step: converting the naturality clause from its
representative form `AcOfFun c (f ∘ b)` to the `ArchNat.AcMap` form of `ArchPlaceDict`, using
`ArchNat.AcMap_AcOfFun` and the surjectivity of `Acπ`.

The statement `archPlaceDict_of_psi` is stated **without reference to the lead's `def`** (the body is
copied verbatim), so it can be used for `ArchPlaceDict … c w` by `delta`/`exact`.
-/

namespace Work.SSGRoute.ArchSplit2

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option linter.unusedVariables false

/-- **`ArchPlaceDict` at a split place, from the canonical `ψ` of A3.**

Body copied verbatim from `Work.SSGRoute.LeadNatWit.ArchPlaceDict` (`_lead_design/ssg_natwit_0820.lean`). -/
theorem archPlaceDict_of_psi
    (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hbot : SSGRoute.PTExt.decompK (k := k) w = ⊥)
    (ψ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        E →+ CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1)
    (hψ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E], Function.Bijective (ψ E))
    (hψnat : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (F' : Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E₂ ⟶
          Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E)
        (hF' : ∀ (θ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E) (t : T),
          (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom θ)
            (TensorProduct.tmul (ZMod p) e t) = θ (TensorProduct.tmul (ZMod p) (f e) t))
        (e : E),
        ψ E₂ (f e) = (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp (ψ E e) (zero_add 1))
    (hψsq : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (b : (Ω ≃ₐ[k] Ω) → E),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        ψ E (b c) = SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))) :
    ∃ Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Work.SSGRoute.ArchDictionary.Ac (K := K) (E := E) c ≃+ CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (b : (Ω ≃ₐ[k] Ω) → E),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          Φ E (Work.SSGRoute.ArchDictionary.AcOfFun (K := K) (E := E) c b) =
            SSGRoute.PTExt.extLoc (k := k) w
              (SSGRoute.PTExt.extToIdeles (k := k)
                (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))) ∧
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂]
          [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
          (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
          (F' : Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E₂ ⟶
            Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E)
          (hF' : ∀ (ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E) (t : T),
            (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom ψ)
              (TensorProduct.tmul (ZMod p) e t) = ψ (TensorProduct.tmul (ZMod p) (f e) t))
          (x : Work.SSGRoute.ArchDictionary.Ac (K := K) (E := E) c),
          Φ E₂ (Work.SSGRoute.ArchNat.AcMap (f : E →+ E₂) (fun g e => hf g e) c x) =
            (CategoryTheory.Abelian.Ext.mk₀
              (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp
              (Φ E x) (zero_add 1)) := by
  classical
  have hbot' : SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite
        (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))) = ⊥ := by
    rw [← hw]; exact hbot
  have hres : SSGRoute.res k K c = 1 :=
    Work.SSGRoute.ArchDictionary.res_eq_one_of_decompK_eq_bot
      (k := k) (K := K) (Ω := Ω) c hc2 hc1 φ hlink hbot'
  obtain ⟨βc, hcl⟩ :=
    splitPlace_family_clause p hp k Ω K ζ hζ hζK T hT c hc2 hc1 φ hlink w hw hbot ψ hψ hψnat hψsq
  have hβc_add : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (b b' : (Ω ≃ₐ[k] Ω) → E),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
      βc E (b + b') = βc E b + βc E b' := fun E _ _ _ _ _ => (hcl E).1
  have hβc_ker : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (b : (Ω ≃ₐ[k] Ω) → E),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
      (βc E b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :=
    fun E _ _ _ _ _ => (hcl E).2.1
  have hβc_onto : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (y : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1),
      ∃ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc E b = y :=
    fun E _ _ _ _ _ => (hcl E).2.2.1
  have hβc_sq : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (b : (Ω ≃ₐ[k] Ω) → E),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      βc E b = SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) :=
    fun E _ _ _ _ _ b hb hl => ((hcl E).2.2.2.1 b hb hl).symm
  have hβc_nat : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
      (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
      (F' : Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E₂ ⟶
        Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E)
      (hF' : ∀ (θ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E) (t : T),
        (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom θ)
          (TensorProduct.tmul (ZMod p) e t) = θ (TensorProduct.tmul (ZMod p) (f e) t))
      (b : (Ω ≃ₐ[k] Ω) → E),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
      βc E₂ (fun σ => f (b σ)) = (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp (βc E b) (zero_add 1) :=
    fun E _ _ _ _ _ E₂ _ _ _ _ _ f hf F' hF' b hb => (hcl E).2.2.2.2 E₂ f hf F' hF' b hb
  obtain ⟨Φ, hsq, hnatRep⟩ :=
    uniformSquare_of_family_clause p hp k Ω K ζ hζ hζK T hT c hc2 hc1 w βc
      hβc_add hβc_ker hβc_onto hβc_sq hβc_nat
  refine ⟨Φ, hsq, ?_⟩
  intro E _ _ _ _ _ E₂ _ _ _ _ _ f hf F' hF' x
  obtain ⟨z, hz⟩ := Work.SSGRoute.ArchDictionary.Acπ_surjective (K := K) (E := E) c x
  have hzF : Work.SSGRoute.ArchDictionary.AcOfFun (K := K) (E := E) c (z : (Ω ≃ₐ[k] Ω) → E) = x := by
    rw [Work.SSGRoute.ArchDictionary.AcOfFun_eq (K := K) (E := E) c _ z.2]
    exact hz
  have hAcMap :
      Work.SSGRoute.ArchNat.AcMap (f : E →+ E₂) (fun g e => hf g e) c x
        = Work.SSGRoute.ArchDictionary.AcOfFun (K := K) (E := E₂) c
            (fun σ => f ((z : (Ω ≃ₐ[k] Ω) → E) σ)) := by
    rw [← hzF]
    exact Work.SSGRoute.ArchNat.AcMap_AcOfFun (f : E →+ E₂) (fun g e => hf g e) c z.2
  rw [hAcMap, hnatRep E E₂ f hf F' hF' (z : (Ω ≃ₐ[k] Ω) → E) z.2, hzF]

end Work.SSGRoute.ArchSplit2
