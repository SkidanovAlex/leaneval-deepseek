import Mathlib
import Submission.Work.SSGRoute.E1aClean.localDictionary_natural_family
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The natural global/local dictionary family, and its clauses

`Work.SSGRoute.E1aClean.localDictionary_natural_family` produces the *canonical* pair
`(βl, βg)` of dictionaries (local, global) with a list of clauses.  This file

* names the chosen pair (`natFamβl`, `natFamβg`), and
* extracts **each clause separately**, in the exact spelling in which the consumers
  (`PT.finHalfData.finZB` after its re-basing, `PT.G1plusOwn.levelFree.isCoboundaryOn_of_finZB_eq_zero`,
  the COUNT route's `hβg_sq` / `hβg_unr`) need it.

The extraction is `Classical.choose_spec`; nothing here is new mathematics.
-/

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.E1aClean

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- The canonical **local** dictionary `βl` chosen by `localDictionary_natural_family`. -/
noncomputable def natFamβl :=
  Classical.choose (localDictionary_natural_family p k Ω K ζ hζ hζK T hT)

/-- The canonical **global** dictionary `βg` chosen by `localDictionary_natural_family`. -/
noncomputable def natFamβg :=
  Classical.choose
    (Classical.choose_spec (localDictionary_natural_family p k Ω K ζ hζ hζK T hT))

/-- The clause list of `localDictionary_natural_family`, for the named pair. -/
theorem natFam_spec :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b' → SSGRoute.IsLocConstOn ⊤ b' →
        natFamβg p k Ω K ζ hζ hζK T hT E (b + b') =
          natFamβg p k Ω K ζ hζ hζK T hT E b + natFamβg p k Ω K ζ hζ hζK T hT E b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        (natFamβg p k Ω K ζ hζ hζK T hT E b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ b)) ∧
      (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E, SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧
        SSGRoute.IsLocConstOn ⊤ b ∧ natFamβg p k Ω K ζ hζ hζK T hT E b = y) ∧
      ∀ (A : ValuationSubring Ω)
        (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        SSGRoute.IsFinPlace k A →
        (∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) →
        (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
            natFamβl p k Ω K ζ hζ hζK T hT E A q (b + b') =
              natFamβl p k Ω K ζ hζ hζK T hT E A q b +
                natFamβl p k Ω K ζ hζ hζK T hT E A q b') ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            (natFamβl p k Ω K ζ hζ hζK T hT E A q b = 0 ↔
              SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)) ∧
        (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧
            natFamβl p k Ω K ζ hζ hζK T hT E A q b = y) ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
            SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
              (SSGRoute.PTExt.extToIdeles (k := k) (natFamβg p k Ω K ζ hζ hζK T hT E b)) =
              natFamβl p k Ω K ζ hζ hζK T hT E A q b) ∧
        (¬ A.valuation (p : Ω) < 1 → ¬ SSGRoute.IsRamifiedIn k K A →
          ∀ b : (Ω ≃ₐ[k] Ω) → E,
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            (∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → b σ = 0) →
            SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite q)
              (natFamβl p k Ω K ζ hζ hζK T hT E A q b)) ∧
        (∀ (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2] [DistribMulAction (K ≃ₐ[k] K) E2]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
            (f : E →ₗ[ZMod p] E2) (_ : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
            (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
                (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) ⟶
              SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
                (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
            (_ : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) (e : E) (t : T),
              (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom φ)
                (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
            (b : (Ω ≃ₐ[k] Ω) → E),
            SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
            SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
            natFamβl p k Ω K ζ hζ hζK T hT E2 A q (fun σ => f (b σ)) =
              (CategoryTheory.Abelian.Ext.mk₀
                (Rep.resMap (SSGRoute.PTExt.decompK (k := k)
                  (NK.GlobalCFT.Place.ofFinite q)).subtype F')).comp
                (natFamβl p k Ω K ζ hζ hζK T hT E A q b) (zero_add 1)) :=
  Classical.choose_spec
    (Classical.choose_spec (localDictionary_natural_family p k Ω K ζ hζ hζK T hT))

/-- The **global** additivity clause. -/
theorem natFamβg_add (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (b b' : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hlb : SSGRoute.IsLocConstOn ⊤ b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b') (hlb' : SSGRoute.IsLocConstOn ⊤ b') :
    natFamβg p k Ω K ζ hζ hζK T hT E (b + b') =
      natFamβg p k Ω K ζ hζ hζK T hT E b + natFamβg p k Ω K ζ hζ hζK T hT E b' :=
  (natFam_spec p k Ω K ζ hζ hζK T hT E).1 b b' hb hlb hb' hlb'

/-- The **global** kernel clause: the dictionary vanishes exactly on coboundaries. -/
theorem natFamβg_ker (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hlb : SSGRoute.IsLocConstOn ⊤ b) :
    natFamβg p k Ω K ζ hζ hζK T hT E b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ b :=
  (natFam_spec p k Ω K ζ hζ hζK T hT E).2.1 b hb hlb

/-- The **global** surjectivity clause. -/
theorem natFamβg_onto (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (y : CategoryTheory.Abelian.Ext
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
      (SSGRoute.PTExt.unitsK k K) 1) :
    ∃ b : (Ω ≃ₐ[k] Ω) → E, SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧
      SSGRoute.IsLocConstOn ⊤ b ∧ natFamβg p k Ω K ζ hζ hζK T hT E b = y :=
  (natFam_spec p k Ω K ζ hζ hζK T hT E).2.2.1 y

/-- The **local** additivity clause. -/
theorem natFamβl_add (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hA : SSGRoute.IsFinPlace k A)
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (b b' : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hlb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b')
    (hlb' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b') :
    natFamβl p k Ω K ζ hζ hζK T hT E A q (b + b') =
      natFamβl p k Ω K ζ hζ hζK T hT E A q b + natFamβl p k Ω K ζ hζ hζK T hT E A q b' :=
  ((natFam_spec p k Ω K ζ hζ hζK T hT E).2.2.2 A q hA hAq).1 b b' hb hlb hb' hlb'

/-- The **local** kernel clause: the local dictionary vanishes exactly on coboundaries. -/
theorem natFamβl_ker (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hA : SSGRoute.IsFinPlace k A)
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hlb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) :
    natFamβl p k Ω K ζ hζ hζK T hT E A q b = 0 ↔
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b :=
  ((natFam_spec p k Ω K ζ hζ hζK T hT E).2.2.2 A q hA hAq).2.1 b hb hlb

/-- The **local** surjectivity clause. -/
theorem natFamβl_onto (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hA : SSGRoute.IsFinPlace k A)
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (y : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
      (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 1) :
    ∃ b : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧
      natFamβl p k Ω K ζ hζ hζK T hT E A q b = y :=
  ((natFam_spec p k Ω K ζ hζ hζK T hT E).2.2.2 A q hA hAq).2.2.1 y

/-- The **square**: the localisation of the global dictionary is the local dictionary.  This is the
`hβg_sq` hypothesis of the COUNT route (`finiteS_converse_canonical_v2`). -/
theorem natFam_square (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hA : SSGRoute.IsFinPlace k A)
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hlb : SSGRoute.IsLocConstOn ⊤ b) :
    SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
      (SSGRoute.PTExt.extToIdeles (k := k) (natFamβg p k Ω K ζ hζ hζK T hT E b)) =
      natFamβl p k Ω K ζ hζ hζK T hT E A q b :=
  ((natFam_spec p k Ω K ζ hζ hζK T hT E).2.2.2 A q hA hAq).2.2.2.1 b hb hlb

/-- The **unramified clause**: a cocycle vanishing on the inertia at a good place has an unramified
local dictionary class. -/
theorem natFam_unramified (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hA : SSGRoute.IsFinPlace k A)
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (hp : ¬ A.valuation (p : Ω) < 1) (hram : ¬ SSGRoute.IsRamifiedIn k K A)
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hlb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hiner : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k A σ → b σ = 0) :
    SSGRoute.PTExt.IsUnramifiedExt (NK.GlobalCFT.Place.ofFinite q)
      (natFamβl p k Ω K ζ hζ hζK T hT E A q b) :=
  ((natFam_spec p k Ω K ζ hζ hζK T hT E).2.2.2 A q hA hAq).2.2.2.2.1 hp hram b hb hlb hiner

/-- The **naturality** clause in the coefficient module. -/
theorem natFam_natural (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hA : SSGRoute.IsFinPlace k A)
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2] [DistribMulAction (K ≃ₐ[k] K) E2]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
    (f : E →ₗ[ZMod p] E2) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) ⟶
      SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    (hF' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) (e : E) (t : T),
      (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom φ)
        (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
    (b : (Ω ≃ₐ[k] Ω) → E)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hlb : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b) :
    natFamβl p k Ω K ζ hζ hζK T hT E2 A q (fun σ => f (b σ)) =
      (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite q)).subtype F')).comp
        (natFamβl p k Ω K ζ hζ hζK T hT E A q b) (zero_add 1) :=
  ((natFam_spec p k Ω K ζ hζ hζK T hT E).2.2.2 A q hA hAq).2.2.2.2.2 E2 f hf F' hF' b hb hlb

end

end Work.SSGRoute.E1aClean
