import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.homRep_dualMod_units_localClosure
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.E1aClean.Transport
import Submission.Work.SSGRoute.localField_subfield_place_compat
import Submission.Work.SSGRoute.local_ext_h1_bridge
import Submission.Work.SSGRoute.PT.e1a_coeff_iso_natural
import Submission.Work.SSGRoute.E1aClean.coeffIsoNatural_generic
import Submission.Work.SSGRoute.E1aClean.h1locCoeffNatural
import Submission.Work.SSGRoute.E1aClean.LocalData
import Submission.Work.SSGRoute.E1aClean.localClosureCyclotomicDual
import Submission.Work.SSGRoute.E1aClean.h1AddEquivNat
import Submission.Work.SSGRoute.E1aClean.localExtTransportEquiv
import Submission.Work.SSGRoute.E1aClean.h1contIsoNamed
import Submission.Work.SSGRoute.E1aClean.localDictFromFamily
import Submission.Work.SSGRoute.E1aClean.decompDatum
import Submission.Work.SSGRoute.E1aClean.decompDatumFacts
import Submission.Work.SSGRoute.E1aClean.LocalExtensionAux
import Submission.Work.SSGRoute.E1aClean.decompField_embeds_completion
import Submission.Work.SSGRoute.E1aClean.unitsQuotient_pow_bijective_fixed
import Submission.Work.SSGRoute.ext_res_mulEquiv
import Submission.Work.SSGRoute.E1aClean.globalDictionaryCanonDefs
import Submission.Work.SSGRoute.E1aClean.LeadNatWit
import Submission.Work.SSGRoute.E1aClean.finPlaceDictHolds
import Submission.Work.SSGRoute.ArchDictionary.archimedeanDictionaryCanon
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead guidance. The design is in the workspace at _lead_design/ssg_pt_design_1002/DESIGN.md. Read the section for your statement FIRST (§2 C6 via the induced module from the normal closure of inertia; §3 CRUX-a 3-step; §4 G1+COUNT via the canonical class-formation pairing). It gives the proof route as numbered steps and the proved workspace names to reuse (local_duality_ext_in, detectsAt_of_coeff_surjection, grunwald_over_K_general, countingIdentity_of_reciprocity_and_converse, ...). Do not re-derive what is proved.
Memory: Lean only through the harness; no sleep loops around lake.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

/-! ## The named (canonical) global dictionary

Moved to the sibling module `E1aClean/globalDictionaryCanonDefs.lean` (lead ruling
`_lead_design/ssg_natwit_0820.md`, STEP 0) so that the per-place-witness definitions the lead
installs on top of `globalDictionaryCanon` do not import this file.  The names
`globalDictEquivCanon`, `globalDictionaryCanon`, `globalDictionaryCanon_spec` and
`h1AddEquiv_symm_eq_mapH1` are re-exported here through that import. -/

/-- The natural local dictionary family with the archimedean dictionaries, version 2 (restates
`E1aClean.localDictionary_natural_family_arch`; flags_1730).

Two changes to the archimedean conjunct, everything else verbatim (so the conjunct order, and hence
`finHalfData`'s `.2.2.2.2` projection, is unchanged).
* The place is no longer existential.  For every involution `c ≠ 1` and EVERY embedding
  `φ : Ω →+* ℂ` with `φ ∘ c = conj ∘ φ` (the seam), the clauses hold at `w = mk (φ|_K)`.  So a
  consumer may fix its own `wc c`/`φc c` (from `ArchPlace.linkedPlaceOfInvolution`), the place does
  not depend on the coefficient module `E`, and two involutions are attached to the places they
  actually induce.  `D_w = ⟨res c⟩` and `w` infinite are no longer clauses: they follow from the seam
  (`decompK_linked`).
* New naturality clause for `βc`, the mirror of the `βl` clause: for `f : E → E₂` equivariant and the
  transpose `F' : E₂' ⟶ E'`, `βc E₂ c w (f ∘ b) = F'^* (βc E c w b)`.  This is what clause (5) of G1⁺
  needs at involution groups for the swapped pairing.

Route: as before (flags_0030 §3).  `βc E c w` is `E1cGeneric` at `(Ω^{⟨c⟩}, Ω, K·Ω^{⟨c⟩})`, pushed
along `φ : Ωˣ → ℂˣ` (an isomorphism on `Ext` of p-torsion, since `ℂˣ/φ(Ωˣ)` is uniquely
divisible).  Independence of the choice of `φ` is not needed: the clauses are proved for each `φ`.
Naturality is the same four-factor chase as for `βl` (`e1cMap_natural`, `h1AddEquiv_natural`,
`coeffIso_natural_generic`, and the push, which is natural in the coefficients). -/
theorem localDictionary_natural_family_arch (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
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
                (βl E A q b) (zero_add 1)) :=
  Work.SSGRoute.LeadNatWit.natural_family_arch_of_perPlace p k Ω K ζ hζ hζK T hT
    (fun A hA q hAq =>
      Work.SSGRoute.E1aClean.finPlaceDict_holds p k Ω K ζ hζ hζK T hT A hA q hAq)
    (Work.SSGRoute.ArchDictionary.archPlaceDict_holds p k Ω K ζ hζ hζK T hT)


/-- The natural local dictionary family with its global square (strengthened `S6`).

One family `βl E A q` of local dictionaries `Z¹(D_A, E) → Ext¹_{D_q}(E', K_qˣ)`
(`E' = DualMod p (E ⊗ T)`) and one family `βg E` of global dictionaries
`Z¹(G_k, E) → Ext¹_{Gal(K/k)}(E', Kˣ)`, indexed by the finite module `E`, such that for every `E`:
the global and local dictionaries are additive, have kernel the coboundaries, and are onto; the
square `extLoc q (extToIdeles (βg E b)) = βl E A q b` holds for global cocycles `b`; a local
cocycle vanishing on inertia at a good place (not over `p`, unramified in `K`) goes to an
unramified class; and the local dictionaries are natural: for `f : E → E₂` equivariant and the
transpose `F' : E₂' ⟶ E'` of `f ⊗ id_T`, `βl E₂ A q (f ∘ a) = F'^* (βl E A q a)`.

These three extra clauses (unramified, natural, square) are exactly what the Yoneda-defined
canonical pairing of `G1_followup.md` needs beyond the proved `local_duality_ext_in`: naturality gives
clause (5), the unramified clause gives clause (6) with `levelPair_unramified_eq_zero`, the square
gives reciprocity (7) and the converse (8).

Route (shared with `E1aClean.finLocalCriterion`).  Build both dictionaries by one recipe from the
functorial free cover `0 → R → Rep.free (E'.V) → E' → 0` (`Work.SSGRoute.freeCover`,
`PT.freeCoverSESMap` for functoriality): `Ext¹(E', U) = coker(Hom(F, U) → Hom(R, U))` for
`U = Kˣ` (Hilbert 90) and for `U = K_qˣ` (local Hilbert 90), and `H¹(·, E)` is the same cokernel with
`U = Ωˣ`, resp. the decomposition field `K^h ⊂ Ω` pushed into `K_q`.  The cocycle attached to
`ψ ∈ Hom(R, U)` is `g ↦ g·ψ̃ − ψ̃` for any extension `ψ̃` to `F` (`Ωˣ` divisible).  Naturality:
`freeCoverSESMap`.  Square: the same formula restricted to `D_A`.  Unramified clause: if the cocycle
vanishes on inertia, `ψ̃` can be chosen with values in the integral units over the maximal unramified
extension, so the class comes from `𝒪_qˣ`.  Bijectivity of the local dictionary can be copied from
the proof of `local_ext_h1_bridge`. -/
theorem localDictionary_natural_family (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
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
            (SSGRoute.PTExt.unitsK k K) 1),
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
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
  obtain ⟨βl, βg, βc, hβ⟩ :=
    localDictionary_natural_family_arch p k Ω K ζ hζ hζK T hT
  refine ⟨βl, βg, ?_⟩
  exact fun E => ⟨(hβ E).2.1, (hβ E).2.2.1, (hβ E).2.2.2.1, (hβ E).2.2.2.2⟩

end Work.SSGRoute.E1aClean
