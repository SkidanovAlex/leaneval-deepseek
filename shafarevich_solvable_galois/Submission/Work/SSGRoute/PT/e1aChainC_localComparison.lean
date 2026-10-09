import Mathlib
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.local_ext_h1_bridge
import Submission.Work.SSGRoute.PT.e1aBetaCan_localDictionary_fin_compat
import Submission.Work.SSGRoute.localField_subfield_place_compat
import Submission.Work.SSGRoute.E1aClean.Reductions
import Submission.Work.SSGRoute.E1aClean.landingFinCompat_from_criterion
import Submission.Work.SSGRoute.E1aClean.finLocalCriterion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The per-place local comparison for the canonical chain `e1aChainC`

## What this file is

`Work.SSGRoute.PT.e1aChainC_localComparison` is the *per-place* form of the localisation clause of
E1a (`PT/NOTE_e1aBetaCan_le_ker.md`, and the review notes of this node):

> if `e1aChainC y` has a continuous `2`-cocycle representative which is a coboundary (with a
> locally constant primitive) on the decomposition group `D_A` of a finite place `A` of `Ω`, then
> the component `extLoc_q (extToIdeles y)` of `y` at the place `q` of `K` under `A` vanishes.

By §4 of `PT/NOTE_e1aBetaCan_le_ker.md` this is the shape the landing clause consumes *place by
place* (the sibling node `PT/e1aBetaCan_splitPlaces` disposes of the places with `decompK w = ⊥`;
the involution/archimedean places are a separate sibling).

## What is proved here, and what is not

* **Proved here** (`classLevel_of_cocycleLevel`): the *cocycle-level* hypothesis of the target
  implies the *class-level* hypothesis used by the sibling dictionary statements, i.e.

      (∃ c ∈ Z²_c(G_k,E),  H2π c = e1aChainC y ∧ c|D_A ∈ B²_c(D_A))
        →  resH2_{D_A} (akToGCH2 (e1aChainC y)) = 0.

  `⟸` fails (the class-level cobounding is only an *abstract* one, `resH2_akToGCH2_H2π_eq_zero_iff`
  of `PT/e1aBetaCan_localDictionary_fin_compat`), so the target is *strictly weaker* than the
  class-level statements `PT/e1aBetaCan_localDictionary_fin_inj` /
  `PT/e1aBetaCan_localDictionary_fin_compat`, and is implied by the *conjunction* of

    (`classCompat`)  ∀ y, resH2_{D_A} (akToGCH2 (e1aChainC y)) = 0 → extLoc_q (extToIdeles y) = 0,

  with the reduction above.  This file closes the reduction and records precisely what is missing.

* **Not proved here** (the target itself): `classCompat` is the missing comparison square of the
  E1a lane.  See the note `PT/NOTE_e1aChainC_localComparison.md` for the exact reformulation and the
  two missing inputs (the choice-free degree-two local dictionary at the completion, and its
  compatibility with the canonical global chain).

## The reduction, in the language of the dictionary

Writing `y = e1aSyzShift z` (`z ∈ Ext¹_G(R, Kˣ)`, `R` the canonical syzygy) and `ζ = e1cEquiv` for
the canonical `E1c` dictionary, the hypothesis of the target is *equivalent* (by the injectivity of
`e1aCoeffH2`, of the connecting map `δ` and of `δ|_{D_A}`, the latter by Shapiro's lemma) to

      res_{D_A} (ζ z) = 0   in   H¹(D_A, Hom_ℤ(R|, Ωˣ)),

while its conclusion is *equivalent* (by the naturality of the syzygy shift under restriction and
the associativity of the Yoneda product) to `z_w = 0`, where

      z_w := (extRes_{D_w} z) ∘ (mk₀ (Kˣ → K_wˣ)) ∈ Ext¹_{D_w}(R|, K_wˣ).

So the target is exactly the statement that the two localisations of the *canonical* class agree —
the "comparison square" whose two halves are recorded in the note.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-- **The reduction.**  The cocycle-level hypothesis of `e1aChainC_localComparison` implies the
class-level hypothesis used by the dictionary statements: if `e1aChainC y` has a continuous
representative `c` which is a coboundary on `D_A` (with a locally constant primitive), then
`resH2_{D_A} (akToGCH2 (e1aChainC y)) = 0`. -/
theorem classLevel_of_cocycleLevel (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2) :
    (∃ c : @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
          (DistribMulAction.compHom E (SSGRoute.res k K)),
        @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K)) c =
          Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y ∧
        SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A)
          (fun g h => c.1 (g, h))) →
      @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (SSGRoute.decomp k A)
        (@Work.SSGRoute.PT.akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
          (DistribMulAction.compHom E (SSGRoute.res k K))
          (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)) = 0 := by
  rintro ⟨c, hc, hcob⟩
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  letI : DistribMulAction ↥(SSGRoute.decomp k A) E :=
    Subgroup.instDistribMulActionSubtypeMem (SSGRoute.decomp k A)
  rw [← hc]
  rw [Work.SSGRoute.PT.resH2_akToGCH2_H2π_eq_zero_iff]
  obtain ⟨b, _hb, hbc⟩ := hcob
  refine ⟨fun g => b (g : Ω ≃ₐ[k] Ω), ?_⟩
  ext p
  rw [show (Work.GroupCohomology.d1 ↥(SSGRoute.decomp k A) E
        (fun g => b (g : Ω ≃ₐ[k] Ω))) p
      = (SSGRoute.res k K) (p.1 : Ω ≃ₐ[k] Ω) • b (p.2 : Ω ≃ₐ[k] Ω)
        - b ((p.1 : Ω ≃ₐ[k] Ω) * (p.2 : Ω ≃ₐ[k] Ω)) + b (p.1 : Ω ≃ₐ[k] Ω) from rfl]
  simp only [Work.GroupCohomology.resZ2_coe, Work.GroupCohomology.resCochain2_apply,
    Work.SSGRoute.PT.akZ2ToGCZ2_coe]
  exact (hbc (p.1 : Ω ≃ₐ[k] Ω) p.1.2 (p.2 : Ω ≃ₐ[k] Ω) p.2.2).symm

end

end Work.SSGRoute.PT

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

noncomputable section


/-- **Assembly**: the target follows from the *class-level* comparison
`∀ y, resH2_{D_A} (akToGCH2 (e1aChainC y)) = 0 → extLoc_q (extToIdeles y) = 0`
(this is the missing comparison square of the E1a lane; it is the content of the sibling nodes
`PT/e1aBetaCan_localDictionary_fin_inj` / `..._fin_compat`), together with the reduction
`classLevel_of_cocycleLevel` proved above. -/
theorem e1aChainC_localComparison_of_classLevel (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (hclass : ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
        (DistribMulAction.compHom E (SSGRoute.res k K))
        (SSGRoute.decomp k A)
        (@Work.SSGRoute.PT.akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
          (DistribMulAction.compHom E (SSGRoute.res k K))
          (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)) = 0 →
      SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
        (SSGRoute.PTExt.extToIdeles (k := k) y) = 0) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      (∃ c : @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K)),
          @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
              (DistribMulAction.compHom E (SSGRoute.res k K)) c =
            Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y ∧
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A)
            (fun g h => c.1 (g, h))) →
        SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
          (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 :=
  fun y hy => hclass y (classLevel_of_cocycleLevel p k Ω K ζ hζ hζK T hT E A hA q hAq y hy)

/-- **The per-place local comparison** (the target of this node). -/
theorem e1aChainC_localComparison (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    ∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
      (∃ c : @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K)),
          @Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
              (DistribMulAction.compHom E (SSGRoute.res k K)) c =
            Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y ∧
          SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A)
            (fun g h => c.1 (g, h))) →
        SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofFinite q)
          (SSGRoute.PTExt.extToIdeles (k := k) y) = 0 := by
  intro y hy
  obtain ⟨c, hc, hcob⟩ := hy
  exact Work.SSGRoute.E1aClean.e1aLandingFinCompat_of_criterion p k Ω K ζ hζ hζK T hT E A hA q hAq y
    (Work.SSGRoute.E1aClean.akRes_e1aChainC_eq_zero_of_coboundary p k Ω K ζ hζ hζK T hT E y A hA
      c hc hcob)

end

end Work.SSGRoute.PT


/-! ## The local data of E7a: its closure is already an algebraic closure

`NK.FrobeniusBridge.localClosure A = SeparableClosure (localField A)`, so `localClosureAt k A hA`
is *algebraic* over `localFieldAt k A hA`; in characteristic `0` a separably closed algebraic
extension is algebraically closed.  These are exactly the instances that the generic canonical
chapter `E1cGeneric.Canonical` (and `ext_continuous_descent_fg_homCoind`) need in order to be
instantiated at E7a's local data `(k_v, Ω_v, K_w)`; they are exported here so that the
localisation comparison does not have to re-derive them (see
`PT/NOTE_e1aChainC_localComparison.md` §11.7). -/

namespace Work.SSGRoute.PT

/-- **E7a's local closure is an algebraic closure of the local field.**
`localClosureAt k A hA` is the separable closure of `localFieldAt k A hA`
(`NK.FrobeniusBridge.localClosure`), hence algebraic over it, and in characteristic `0` a
separably closed algebraic extension is algebraically closed
(`IsSepClosure.isAlgClosure_of_perfectField` with `PerfectField.ofCharZero`). -/
theorem isAlgClosure_localClosureAt (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    IsAlgClosure (Work.SSGRoute.localFieldAt k A hA) (Work.SSGRoute.localClosureAt k A hA) :=
  inferInstance

/-- E7a's local closure is algebraic over the local field (the `Algebra.IsAlgebraic` half). -/
theorem localClosureAt_isAlgebraic (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Algebra.IsAlgebraic (Work.SSGRoute.localFieldAt k A hA)
      (Work.SSGRoute.localClosureAt k A hA) :=
  inferInstance

/-- **The first variable of the local dictionary**: the global coefficient module `X = E^∨(1)`
restricted to the decomposition group `D_w` and transported along `eG : D_w ≃* Gal(K'/L)`.  This is
the `X'` of `PT/NOTE_e1aChainC_localComparison.md` §9 and §11. -/
noncomputable abbrev localFirstVar {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) {L M : Type} [Field L] [Field M] [Algebra L M]
    (K' : IntermediateField L M) (eG : ↥(SSGRoute.PTExt.decompK (k := k) w) ≃* (K' ≃ₐ[L] K'))
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    Rep.{0} SSGRoute.PTExt.Coeff (K' ≃ₐ[L] K') :=
  Rep.res eG.symm.toMonoidHom (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype X)

/-- The underlying type of the local first variable is the underlying type of `X`. -/
theorem localFirstVar_V {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) {L M : Type} [Field L] [Field M] [Algebra L M]
    (K' : IntermediateField L M) (eG : ↥(SSGRoute.PTExt.decompK (k := k) w) ≃* (K' ≃ₐ[L] K'))
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    (localFirstVar (k := k) w K' eG X).V = X.V :=
  rfl

/-- Finiteness of the local first variable, from finiteness of `X`. -/
theorem finite_localFirstVar {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) {L M : Type} [Field L] [Field M] [Algebra L M]
    (K' : IntermediateField L M) (eG : ↥(SSGRoute.PTExt.decompK (k := k) w) ≃* (K' ≃ₐ[L] K'))
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (h : Finite X.V) :
    Finite (localFirstVar (k := k) w K' eG X).V :=
  h

/-- `Module.Finite ℤ` of the local first variable, from the same for `X`. -/
theorem module_finite_localFirstVar {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) {L M : Type} [Field L] [Field M] [Algebra L M]
    (K' : IntermediateField L M) (eG : ↥(SSGRoute.PTExt.decompK (k := k) w) ≃* (K' ≃ₐ[L] K'))
    (X : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ X.V] :
    Module.Finite ℤ (localFirstVar (k := k) w K' eG X).V :=
  ‹_›

end Work.SSGRoute.PT
