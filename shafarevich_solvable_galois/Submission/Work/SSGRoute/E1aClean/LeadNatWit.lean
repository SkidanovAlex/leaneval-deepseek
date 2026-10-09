import Mathlib
/- Lead-installed 10-07 (design _lead_design/ssg_natwit_0820.md): per-place reduction of localDictionary_natural_family_arch. Built on globalDictionaryCanonDefs, NOT on the leaf (avoids an import cycle). -/
import Submission.Work.SSGRoute.E1aClean.globalDictionaryCanonDefs
import Submission.Work.SSGRoute.E1aClean.localDictFromFamily
import Submission.Work.SSGRoute.ArchNat.archUniformNatural
import Submission.Work.SSGRoute.ext_res_mulEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
-- (cut 4 of `ACTION_leaf_endgame_cycles_and_cut_list.md`): `PT.archβcClauses` was imported only for
-- the trailing `#typeTaint Work.SSGRoute.PT.archβc_natural` diagnostic (also removed below); the
-- import dragged the leaf `E1aClean.localDictionary_natural_family_arch` into `cone(LeadNatWit)`.

/-! Lead design ssg_natwit_0820 (see ssg_natwit_0820.md).

(1) `FinPlaceDict` / `ArchPlaceDict`: per-place, `E`-INDEXED dictionary data carrying EVERY clause
    the leaf needs (finite: naturality + square + unramified; archimedean: square + naturality).
(2) `natural_family_arch_of_perPlace` (PROVED below): the body of
    `E1aClean.localDictionary_natural_family_arch` follows from (1) at every place.  The per-place
    witnesses are taken with `Classical.choose` -- per PLACE, never per `E` -- and that is harmless,
    because every clause of the leaf at a place only involves the family at that place.
(3) `extResEquivExplicit`: the explicit form of `ext_res_mulEquiv` (which is a bare `Nonempty`). -/

namespace Work.SSGRoute.LeadNatWit

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

/-- Finite place `(A,q)`: an `E`-indexed local dictionary `Φ`, natural, with the global square and
the unramified clause.  (= `ArchNat.exists_localDictPhi_natural_and_square` + unramified.) -/
def FinPlaceDict (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) : Prop :=
  ∃ Φ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Work.SSGRoute.H1loc p k Ω K E (SSGRoute.decomp k A) ≃+
        Work.SSGRoute.E1aClean.localExt p k Ω K T A q E,
    -- naturality
    (∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
      (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
      (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
      (F : Work.SSGRoute.H1loc p k Ω K E₁ (SSGRoute.decomp k A) →+
            Work.SSGRoute.H1loc p k Ω K E₂ (SSGRoute.decomp k A))
      (hF1 : ∀ (b : (Ω ≃ₐ[k] Ω) → E₁)
        (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
        (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b),
        F (Work.SSGRoute.toClass p k Ω K E₁ (SSGRoute.decomp k A) b) =
          Work.SSGRoute.toClass p k Ω K E₂ (SSGRoute.decomp k A) (fun g => f (b g)))
      (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) ⟶
          SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))
      (hF' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
        (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T) from F'.hom φ)
          (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
      (x : Work.SSGRoute.H1loc p k Ω K E₁ (SSGRoute.decomp k A)),
      (Φ E₂) (F x) =
        (CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite q)).subtype F')).comp
          ((Φ E₁) x) (zero_add 1)) ∧
    -- the square with the canonical global dictionary
    (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (b : (Ω ≃ₐ[k] Ω) → E),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))
        = Φ E (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b)) ∧
    -- unramified classes
    (¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (b : (Ω ≃ₐ[k] Ω) → E),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
        (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → b σ = 0) →
        SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite q)
          (Φ E (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b)))

/-- Archimedean place `w` of the involution `c`: verbatim the `hsq` input of the PROVED
`ArchNat.archimedeanDictUniformNat`. -/
def ArchPlaceDict (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (w : NK.GlobalCFT.Place ↥K) : Prop :=
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
            (Φ E x) (zero_add 1))

set_option linter.unusedVariables false

/-- **The leaf from per-place data.**  The body of `E1aClean.localDictionary_natural_family_arch`,
verbatim, from `FinPlaceDict` at every finite place and `ArchPlaceDict` at every seam place. -/
theorem natural_family_arch_of_perPlace (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hfin : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ∀ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      (∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) →
      FinPlaceDict p k Ω K ζ hζ hζK T hT A q)
    (harch : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ φ : Ω →+* ℂ,
      (∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) → ∀ w : NK.GlobalCFT.Place ↥K,
      w = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω))) →
      ArchPlaceDict p k Ω K ζ hζ hζK T hT c w) :
    ∃ (βl : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (_ : ValuationSubring Ω)
          (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
          ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
            (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
              (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
            (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 1)
      (βg : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
          ((Ω ≃ₐ[k] Ω) → E) →
          CategoryTheory.Abelian.Ext (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
            (SSGRoute.PTExt.unitsK k K) 1)
      (βc : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (_ : (Ω ≃ₐ[k] Ω)) (w : NK.GlobalCFT.Place ↥K),
          ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
            (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
              (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
            (SSGRoute.PTExt.localUnitsK (k := k) w) 1),
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      -- archimedean dictionaries: at the place linked to `c` by ANY seam embedding `φ`
      (∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 → ∀ φ : Ω →+* ℂ, (∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) →
          (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
            βc E c (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω)))) (b + b') =
              βc E c (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω)))) b +
              βc E c (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω)))) b') ∧
          (∀ b : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
            (βc E c (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω)))) b = 0 ↔
              SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) ∧
          (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧
            βc E c (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω)))) b = y) ∧
          (∀ b : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
            SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω))))
              (SSGRoute.PTExt.extToIdeles (k := k) (βg E b)) =
              βc E c (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω)))) b) ∧
          -- naturality in the coefficient module (mirror of the `βl` clause)
          (∀ (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2] [DistribMulAction (K ≃ₐ[k] K) E2]
            [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
              (f : E →ₗ[ZMod p] E2) (_ : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
              (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) ⟶
                SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
              (_ : ∀ (ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) (e : E) (t : T),
                (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom ψ)
                  (TensorProduct.tmul (ZMod p) e t) = ψ (TensorProduct.tmul (ZMod p) (f e) t))
              (b : (Ω ≃ₐ[k] Ω) → E),
              SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
              βc E2 c (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω))))
                  (fun σ => f (b σ)) =
                (CategoryTheory.Abelian.Ext.mk₀
                  (Rep.resMap (SSGRoute.PTExt.decompK (k := k)
                    (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω))))).subtype F')).comp
                  (βc E c (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω)))) b)
                  (zero_add 1))) ∧
      -- global dictionary
      (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b' → SSGRoute.IsLocConstOn ⊤ b' →
        βg E (b + b') = βg E b + βg E b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        (βg E b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ b)) ∧
      (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E, SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧
        SSGRoute.IsLocConstOn ⊤ b ∧ βg E b = y) ∧
      ∀ (A : ValuationSubring Ω) (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        SSGRoute.IsFinPlace k A →
        (∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) →
        -- local dictionary
        (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
            βl E A q (b + b') = βl E A q b + βl E A q b') ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            (βl E A q b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)) ∧
        (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ βl E A q b = y) ∧
        -- the square
        (∀ b : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
            SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
              (SSGRoute.PTExt.extToIdeles (k := k) (βg E b)) = βl E A q b) ∧
        -- unramified classes
        (¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
          ∀ b : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → b σ = 0) →
            SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite q) (βl E A q b)) ∧
        -- naturality in the coefficient module
        (∀ (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2] [DistribMulAction (K ≃ₐ[k] K) E2]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
            (f : E →ₗ[ZMod p] E2) (_ : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
            (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) ⟶
              SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
            (_ : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) (e : E) (t : T),
              (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom φ)
                (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
            (b : (Ω ≃ₐ[k] Ω) → E),
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            βl E2 A q (fun σ => f (b σ)) =
              (CategoryTheory.Abelian.Ext.mk₀
                (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype F')).comp
                (βl E A q b) (zero_add 1)) := by
  classical
  -- the archimedean witness at `(c,w)`: chosen per PLACE (φ₀ := any seam embedding inducing `w`)
  let P : (Ω ≃ₐ[k] Ω) → NK.GlobalCFT.Place ↥K → Prop := fun c w =>
    c ^ 2 = 1 ∧ c ≠ 1 ∧ ∃ φ : Ω →+* ℂ, (∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) ∧
      w = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω)))
  have archThm := fun (c : Ω ≃ₐ[k] Ω) (w : NK.GlobalCFT.Place ↥K) (h : P c w) =>
    Work.SSGRoute.ArchNat.archimedeanDictUniformNat p k Ω K ζ hζ hζK T hT c h.1 h.2.1 w
      (Classical.choose h.2.2)
      (fun q hq => NK.GlobalCFT.Place.ofInfinite_ne_ofFinite _ q
        (((Classical.choose_spec h.2.2).2).symm.trans hq))
      (Classical.choose_spec h.2.2).2 (Classical.choose_spec h.2.2).1
      (harch c h.1 h.2.1 _ (Classical.choose_spec h.2.2).1 w (Classical.choose_spec h.2.2).2)
  let βc : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (_ : (Ω ≃ₐ[k] Ω)) (w : NK.GlobalCFT.Place ↥K),
      ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1 :=
    fun E _ _ _ _ _ c w b => if h : P c w then Classical.choose (archThm c w h) E b else 0
  -- the finite witness at `(A,q)`: chosen per PLACE
  let Q : ValuationSubring Ω → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) →
      Prop := fun A q => SSGRoute.IsFinPlace k A ∧
        (∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
  let βl : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
      (_ : ValuationSubring Ω)
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 1 :=
    fun E _ _ _ _ _ A q b => if h : Q A q then
      Classical.choose (hfin A h.1 q h.2) E (Work.SSGRoute.toClass p k Ω K E (SSGRoute.decomp k A) b)
      else 0
  refine ⟨βl, fun E _ _ _ _ _ => Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E,
    βc, ?_⟩
  intro E _ _ _ _ _
  have hg := Work.SSGRoute.E1aClean.globalDictionaryCanon_spec p k Ω K ζ hζ hζK T hT E
  refine ⟨?_, hg.1, hg.2.1, hg.2.2, ?_⟩
  · -- archimedean conjunct
    intro c hc2 hc1 φ hφ
    have h : P c (NK.GlobalCFT.Place.ofInfinite
        (NumberField.InfinitePlace.mk (φ.comp (algebraMap (↥K) Ω)))) := ⟨hc2, hc1, φ, hφ, rfl⟩
    have spec := Classical.choose_spec (archThm c _ h) E
    simp only [βc, dif_pos h]
    exact spec
  · -- finite conjunct
    intro A q hA hAq
    have h : Q A q := ⟨hA, hAq⟩
    have spec := Classical.choose_spec (hfin A hA q hAq)
    have hs := Work.SSGRoute.E1aClean.beta_l_spec p k Ω K T A q
      (Classical.choose (hfin A hA q hAq)) E
    simp only [βl, dif_pos h]
    refine ⟨hs.1, hs.2.1, hs.2.2, ?_, ?_, ?_⟩
    · exact spec.2.1 E
    · intro hp hram b hb hl hI
      exact spec.2.2 hp hram E b hb hl hI
    · intro E2 _ _ _ _ _ f hf F' hF' b hb hl
      exact Work.SSGRoute.E1aClean.beta_l_natural p k Ω K T A q
        (Classical.choose (hfin A hA q hAq)) spec.1 E E2 f hf F' hF' b hb hl

/-- (3) The explicit form of `ext_res_mulEquiv` (which is only a `Nonempty`): use THIS in the
finite chain, never `Classical.choice (ext_res_mulEquiv …)`. -/
noncomputable def extResEquivExplicit {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y : Rep.{0} SSGRoute.PTExt.Coeff G) :
    CategoryTheory.Abelian.Ext (Rep.res e.symm.toMonoidHom X) (Rep.res e.symm.toMonoidHom Y) 1 ≃+
      CategoryTheory.Abelian.Ext X Y 1 :=
  haveI : (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).IsEquivalence :=
    Work.SSGRoute.resFunctor_isEquivalence e
  (AddEquiv.ofBijective
    ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom X Y 1)
    (Functor.mapExt_bijective_of_preservesProjectiveObjects
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom) X Y 1)).symm

/-- Its computation rule (by `rfl`): the inverse IS `res`-functoriality on `Ext`. -/
theorem extResEquivExplicit_symm_apply {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X Y : Rep.{0} SSGRoute.PTExt.Coeff G) (x : CategoryTheory.Abelian.Ext X Y 1) :
    (extResEquivExplicit e X Y).symm x =
      (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom X Y 1 x := rfl

end Work.SSGRoute.LeadNatWit

#print axioms Work.SSGRoute.LeadNatWit.natural_family_arch_of_perPlace
#print axioms Work.SSGRoute.LeadNatWit.extResEquivExplicit_symm_apply


open Lean Elab Command in
elab "#typeTaint " id:ident : command => do
  let env ← getEnv
  let n := id.getId
  let some ci := env.find? n | throwError "no {n}"
  let consts := ci.type.getUsedConstants
  let mut bad : Array Name := #[]
  for c in consts do
    let axs ← liftCoreM (Lean.collectAxioms c)
    if axs.contains ``sorryAx then bad := bad.push c
  logInfo m!"{n}: type constants with sorryAx = {bad}"
#typeTaint Work.SSGRoute.LeadNatWit.FinPlaceDict
#typeTaint Work.SSGRoute.LeadNatWit.ArchPlaceDict
#typeTaint Work.SSGRoute.LeadNatWit.natural_family_arch_of_perPlace
#typeTaint Work.SSGRoute.LeadNatWit.extResEquivExplicit
#print axioms Work.SSGRoute.LeadNatWit.FinPlaceDict
#print axioms Work.SSGRoute.LeadNatWit.ArchPlaceDict
#print axioms Work.SSGRoute.LeadNatWit.extResEquivExplicit
-- (cut 4) the two former "control" lines referenced constants that are no longer imported here
-- (`E1aClean.localDictionary_natural_family_arch` — the leaf — and `PT.archβc_natural`).
#print axioms Work.SSGRoute.ArchNat.archimedeanDictUniformNat
#print axioms Work.SSGRoute.E1aClean.beta_l_natural
#print axioms Work.SSGRoute.E1aClean.globalDictionaryCanon_spec
