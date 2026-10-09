import Submission.Work.SSGRoute.E1aClean.phiCanDefs
import Submission.Work.SSGRoute.E1aClean.LeadNatWit
import Submission.Work.SSGRoute.E1aClean.decompField_hensel_groupIso
import Submission.Work.SSGRoute.E1aClean.levelTwoCocycleAgrees
import Submission.Work.SSGRoute.E1aClean.henselUnits_push_iso
import Submission.Work.SSGRoute.E1aClean.decompFieldHenselEmb_fixes_decomp
import Submission.Work.SSGRoute.E1aClean.decompFieldHenselEmb_relAlgClosed
import Submission.Work.SSGRoute.E1aClean.decompFieldHenselEmb_algebraMap
import Submission.Work.SSGRoute.E1aClean.unitsQuotient_pow_bijective_fixed
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.decompFieldHenselEmb_units_mem_localUnits_iff
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.phiCan_square
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.phiCan_unramified
import Submission.Work.SSGRoute.PT.E1aFinBox.phiCan_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `finPlaceDict_holds`: the finite-place obligation of `localDictionary_natural_family_arch`

Per the lead's ruling (`_lead_design/ssg_natwit_0820.md`), the leaf follows from
`LeadNatWit.natural_family_arch_of_perPlace` once two `E`-indexed per-place facts are supplied:

* `FinPlaceDict` at every finite place `(A,q)` — **this file**;
* `ArchPlaceDict` at every seam place — L4446.

`FinPlaceDict … A q` is

  `∃ Φ : ∀ E, H1loc(D_A,E) ≃+ Ext¹_{D_q}(res E′,K_qˣ), (naturality) ∧ (square) ∧ (unramified)`,

and the witness is the **definable chain** `E1aClean.phiCan` (`E1aClean/phiCanDefs.lean`):

  `phiCan … E = push_θ ∘ extResEquivExplicit ∘ (e1cEquiv₂)⁻¹ ∘ levelChangeTransferD ∘ h1AddEquiv Φd ∘ bridge`

with `Φd = e1aCoeffNat` (the *same* coefficient transport as `globalDictionaryCanon` — this is what
makes the square provable), `θ` pinned by `θ u = Units.map φ u`, `e` pinned by its restriction
clause, and `hpush` the bijectivity of `(mk₀ θ).postcomp` on `p`-torsion (proof-irrelevant).

## The three clauses of `FinPlaceDict` at `Φ := phiCan`

All three are proved, each in its own module:

1. **naturality** — `Work.SSGRoute.PT.E1aFinBox.phiCan_natural` (eight-factor chase);
2. **the square** — `Work.SSGRoute.E1aClean.LeadPhiUnr.phiCan_square`;
3. **unramified** — `Work.SSGRoute.E1aClean.LeadPhiUnr.phiCan_unramified` (from U4
   `LeadPhiUnr.e1cHensel_comp_val_eq_zero_of_unramified`, which is U1 + U2 + U3).

What is done *here* is the assembly: the pinned datum

* `e`, `he` from `decompField_hensel_groupIso` (`e : D_q ≃* Gal(K^h/k^h)`, `he` = its action on `K`),
* `hφres` from `he` by `levelTwoGroupHom_res`,
* `φ := decompFieldHenselEmb k Ω K A hA q hAq halg : K^h →+* K_q` with
  * `hφ` (agreement with `algebraMap` on `K`) — `decompFieldHenselEmb_algebraMap`,
  * `hφint` (units ↦ local units iff `A`-valuation `1`) — U3,
  * `hfix` (the image of `k^h` is `localAutHom`-fixed) — `decompFieldHenselEmb_fixes_decomp`,
  * `hφinj`, and `hQ` (unique `p`-divisibility of `K_qˣ/φ(K^h)ˣ`) — U2's `hQ`.
* `θ`, `hθ`, `hpush` from `HenUnitsPushTarget` (`henselUnits_push_iso`),
* `hpush` for the `phiCan`-shaped argument, from `hpush'` and the `p`-torsion of
  `DualMod p (E ⊗ T)` (`dualMod_p_smul_eq_zero`).
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The finite-place per-place data of `localDictionary_natural_family_arch`.** -/
theorem finPlaceDict_holds (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1) :
    Work.SSGRoute.LeadNatWit.FinPlaceDict p k Ω K ζ hζ hζK T hT A q := by
  classical
  -- ## the structural instances of the level-2 datum `(k^h, Ω, K^h)`
  haveI hGal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI hAlg : IsAlgClosure ↥(decompField k Ω A) Ω :=
    decompField_isAlgClosure_via k Ω K A rfl
  haveI hFd : FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    henselOverDecomp_finiteDimensional k Ω K A
  haveI hGl : IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) :=
    henselOverDecomp_isGalois k Ω K A
  haveI hNorm : Normal ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) := inferInstance
  haveI hsepK : IsSepClosure ↥K Ω :=
    ⟨(inferInstance : IsSepClosure k Ω).sep_closed, inferInstance⟩
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  -- ## the group isomorphism `D_q ≃* Gal(K^h/k^h)` and its action on `K`
  obtain ⟨e, he⟩ := decompField_hensel_groupIso k Ω K A hA q hAq
  have hφres : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      levelTwoGroupHom k Ω K A hA q hAq e
          (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g) :=
    fun g => levelTwoGroupHom_res k Ω K A hA q hAq e he g
  -- ## the henselisation embedding `φ : K^h →+* K_q`
  have hAqK : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q :=
    Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  letI hAlgebra : Algebra (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK).toAlgebra
  have halg : ∀ z : q.adicCompletion ↥K,
      algebraMap (q.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion q A hAqK z := fun z => rfl
  -- `φ` is written out at every use (`def`s are transparent, so this is cosmetically long but
  -- avoids any `let`-opacity in the `Rep`/`Ext` instance search).
  have hφK : ∀ x : ↥K,
      decompFieldHenselEmb k Ω K A hA q hAq halg
          ⟨(x : Ω), le_henselField k Ω K A x.2⟩
        = algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q)) x :=
    fun x => decompFieldHenselEmb_algebraMap k Ω K A hA q hAq halg x
  have hφint : ∀ x : (↥(henselOverDecomp k Ω K A))ˣ,
      Units.map (decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom x ∈
          NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite q)
        ↔ A.valuation (((x : ↥(henselOverDecomp k Ω K A)) : Ω)) = 1 :=
    LeadPhiUnr.decompFieldHenselEmb_units_mem_localUnits_iff k Ω K A hA q hAq halg
  have hfix : ∀ (τ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
      (x : ↥(decompField k Ω A)),
      NK.HassePrinciple.localAutHom (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) τ
          (decompFieldHenselEmb k Ω K A hA q hAq halg
            ⟨(x : Ω), decompField_le_henselField k Ω K A x.2⟩)
        = decompFieldHenselEmb k Ω K A hA q hAq halg
            ⟨(x : Ω), decompField_le_henselField k Ω K A x.2⟩ :=
    decompFieldHenselEmb_fixes_decomp k Ω K A hA q hAq halg
  have hφinj : Function.Injective (decompFieldHenselEmb k Ω K A hA q hAq halg) :=
    RingHom.injective _
  have hQ : Function.Bijective (fun z : Additive (NK.GlobalCFT.Place.localField ↥K
      (NK.GlobalCFT.Place.ofFinite q))ˣ ⧸
      (MonoidHom.range (Units.map
        (decompFieldHenselEmb k Ω K A hA q hAq halg).toMonoidHom)).toAddSubgroup => p • z) :=
    unitsQuotient_pow_bijective_fixed k Ω K A hA q
      (decompFieldHenselEmb k Ω K A hA q hAq halg) hφinj
      (decompFieldHenselEmb_relAlgClosed k Ω K A hA q hAq halg) p
  -- ## the coefficient push `θ` and its two defining clauses
  obtain ⟨θ, hθ, hpush'⟩ :=
    henselUnits_push_iso k Ω K A hA q hAq e he
      (decompFieldHenselEmb k Ω K A hA q hAq halg) hφK hfix hφinj p hQ
  -- ## `hpush` in the `phiCan` shape: the coefficient is `p`-torsion
  have hpush : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      Function.Bijective ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp
        (Rep.res (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite q)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (add_zero 1)) := by
    intro E _ _ _ _ _
    haveI hDfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
      Work.SSGRoute.PT.finite_dualMod_tensor p E T
    exact hpush' _ hDfin
      (fun x => dualMod_p_smul_eq_zero p (TensorProduct (ZMod p) E T) x)
  -- ## the dictionary and its three clauses
  refine ⟨fun E _ _ _ _ _ =>
      phiCan p k Ω K ζ hζ hζK T hT A hA q hAq e hφres θ hpush E, ?_, ?_, ?_⟩
  · -- (1) naturality in the coefficient
    intro E₁ _ _ _ _ _ E₂ _ _ _ _ _ f hf F hF1 F' hF' x
    exact Work.SSGRoute.PT.E1aFinBox.phiCan_natural p k Ω K ζ hζ hζK T hT A hA q hAq
      e hφres θ hpush E₁ E₂ f hf F hF1 F' hF' x
  · -- (2) the square with the canonical global dictionary
    intro E _ _ _ _ _ b hb hl
    -- the *pinned* square `LeadPhiUnr.phiCan_square`: it takes `[Algebra (q.adicCompletion K)
    -- (placeCompletion A)]` and `halg`, so `φ` is *the* canonical `decompFieldHenselEmb` and not an
    -- arbitrary `K`-embedding.  The arbitrary-`φ` form is FALSE: `hφ` pins `φ` only on `K`, and the
    -- admissible pairs `(φ, θ)` (which all satisfy `hpush`) form a `Gal(K^h/K)`-torsor.
    exact LeadPhiUnr.phiCan_square p k Ω K ζ hζ hζK T hT A hA q hAq e hφres halg θ hθ hpush E b hb hl
  · -- (3) unramified classes
    intro hp hram E _ _ _ _ _ b hb hl hI
    exact LeadPhiUnr.phiCan_unramified p k Ω K ζ hζ hζK T hT A hA q hAq e hφres θ hpush
      (decompFieldHenselEmb k Ω K A hA q hAq halg) hθ hφK hφint hp hram E b hb hl hI

end

end Work.SSGRoute.E1aClean
