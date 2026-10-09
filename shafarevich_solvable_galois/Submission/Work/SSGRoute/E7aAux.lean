import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.DecompAction
import Submission.NK.FrobeniusBridge.Basic
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary vocabulary for `Work.SSGRoute.local_ext_h1_bridge` (E7a)

`decompRep`: a `Gal(K/k)`-module `E`, regarded as a module over the decomposition group
`D_A = decomp k A` through the restriction `res k K`.  The action is
`LTDefs/DecompAction.lean`'s `decompDistribMulAction`, which is a `def` rather than an instance
(it depends on `K`), so it is packaged here into a single `Rep Coeff (D_A)` that statements can
name without `letI` gymnastics.
-/

namespace Work.SSGRoute

open CategoryTheory
open SSGRoute.PTExt

noncomputable section

/-- **A `Gal(K/k)`-module as a module over the decomposition group `D_A`**, via the restriction
action `σ • e = res k K σ • e`.  Its carrier is `E` definitionally. -/
def decompRep (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] (A : ValuationSubring Ω) :
    Rep.{0} Coeff ↥(SSGRoute.decomp k A) :=
  letI : DistribMulAction ↥(SSGRoute.decomp k A) E := decompDistribMulAction K E A
  letI : SMulCommClass ↥(SSGRoute.decomp k A) (ZMod p) E :=
    ⟨fun h c e => smul_comm (SSGRoute.res k K (h : Ω ≃ₐ[k] Ω)) c e⟩
  modRep ↥(SSGRoute.decomp k A) E

@[simp] theorem decompRep_V (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] (A : ValuationSubring Ω) :
    (decompRep p k Ω K E A).V = E := rfl

/-- **The local field of a finite place `A` of `Ω` over `k`**: the `A`-adic completion of `k`
(=`NK.FrobeniusBridge.localField`).  Re-exported here so that statements in `Submission/Work/…`
can name it without importing `Submission.NK.…` directly. -/
abbrev localFieldAt (k : Type) {Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :=
  NK.FrobeniusBridge.localField (⟨A, hA⟩ : NK.FrobeniusBridge.FinitePlaceOf k Ω)

/-- The prime of `k` below a finite place `A` of `Ω` (re-exported from
`Submission.NeukirchUchida.primeOf`; `localFieldAt k A hA` is its `adicCompletion`). -/
abbrev primeUnder (k : Type) {Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
  Submission.NeukirchUchida.primeOf A hA

/-- A separable closure of `localFieldAt k A hA`. -/
abbrev localClosureAt (k : Type) {Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :=
  NK.FrobeniusBridge.localClosure (⟨A, hA⟩ : NK.FrobeniusBridge.FinitePlaceOf k Ω)

/-- The identification of the decomposition group of a finite place `A` of `Ω` with the absolute
Galois group of the local field `localFieldAt k A hA`.  Re-exported from
`NK.FrobeniusBridge.localGaloisEquiv`. -/
noncomputable def localGaloisEquivAt (k : Type) {Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ↥(SSGRoute.decomp k A) ≃*
      (localClosureAt k A hA ≃ₐ[localFieldAt k A hA] localClosureAt k A hA) :=
  NK.FrobeniusBridge.localGaloisEquiv (⟨A, hA⟩ : NK.FrobeniusBridge.FinitePlaceOf k Ω)

/-- The local automorphism of `K_w` attached to an element of the decomposition group
(re-exported from `NK.HassePrinciple.localAutHom`): the canonical
`↥(decompK w) →* (K_w ≃+* K_w)`.  It is injective
(`NK.HassePrinciple.localAutHom_injective`); step 2 of the E7a place glue needs its range to be
exactly the `k`-linear automorphisms. -/
noncomputable abbrev localAutHomAt (k : Type) [Field k] [NumberField k]
    {K : Type} [Field K] [NumberField K] [Algebra k K] (w : NK.GlobalCFT.Place K) :
    MulAction.stabilizer (K ≃ₐ[k] K) w →*
      (NK.GlobalCFT.Place.localField K w ≃+* NK.GlobalCFT.Place.localField K w) :=
  NK.HassePrinciple.localAutHom (K := k) w

/-- `Commons`' `adicCompletionMap` at a pair of primes lying over one another, in the shape used
by the E7a place glue: `𝔭.adicCompletion k →+* q.adicCompletion K` for a finite place `A` of `Ω`
with `𝔭 = primeUnder k A hA` and `q` a prime of `K` lying over `𝔭`. -/
noncomputable abbrev adicCompletionMapAt (k : Type) (Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver (primeUnder k A hA).asIdeal) :
    (primeUnder k A hA).adicCompletion k →+* q.adicCompletion K :=
  Commons.RingTheory.Henselian.adicCompletionMap (primeUnder k A hA) q hq

end

end Work.SSGRoute
