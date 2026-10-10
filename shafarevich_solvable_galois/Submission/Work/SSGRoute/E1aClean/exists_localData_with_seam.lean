import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.localGaloisEquiv_coInAdjoin_compat_general

namespace Work.SSGRoute.E1aClean

set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 400000

theorem exists_localData_with_seam (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA)
        (NK.NeukirchUchida.placeCompletion A) :=
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
      (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q
        (Work.SSGRoute.exists_adicCompletion_algebra_compat k Ω K A hA q hAq).choose).toAlgebra
    ∃ (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
          (Work.SSGRoute.localClosureAt k A hA))
      (_ : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K')
      (_ : IsGalois (Work.SSGRoute.localFieldAt k A hA) K')
      (ψ : ↥K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (q.adicCompletion K))
      (eG : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) ≃*
        (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K'))
      (Φ : ↥(SSGRoute.decomp k A) ≃*
        (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA))
      (e : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω)
            (Work.SSGRoute.primeUnder k A hA) A) →+*
          Work.SSGRoute.localClosureAt k A hA),
      IsHomeomorph (Φ : ↥(SSGRoute.decomp k A) →
          (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA)) ∧
      Nonempty (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q) ≅
        Rep.res eG.toMonoidHom (SSGRoute.PTExt.modRep
          (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') (Additive (Units ↥K')))) ∧
      (∀ (σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) (y : ↥K'),
        (eG σ) y = ψ.symm (NK.HassePrinciple.localAut (K := k) (L := ↥K)
          (NK.GlobalCFT.Place.ofFinite q) σ (ψ y))) ∧
      (∀ (σ : ↥(SSGRoute.decomp k A)) (x : K),
        (Φ σ) (ψ.symm (algebraMap K (q.adicCompletion K) x)) =
          ψ.symm (algebraMap K (q.adicCompletion K)
            ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x))) ∧
      (∀ y : K, ((ψ.symm (algebraMap K (q.adicCompletion K) y) : ↥K') :
          Work.SSGRoute.localClosureAt k A hA) =
        e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
          (Work.SSGRoute.primeUnder k A hA) A (algebraMap K Ω y))) ∧
      (∀ (σ : ↥(SSGRoute.decomp k A)) (y : Ω),
        (Φ σ) (e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
            (Work.SSGRoute.primeUnder k A hA) A y)) =
          e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
            (Work.SSGRoute.primeUnder k A hA) A ((σ : Ω ≃ₐ[k] Ω) y))) := by
  classical
  -- the primeness data and the `k`-compatibility, discharged from `hAq`
  obtain ⟨hLies, hcompat', -⟩ :=
    Work.SSGRoute.exists_adicCompletion_algebra_compat k Ω K A hA q hAq
  have hcompat : ∀ x : k, algebraMap k (q.adicCompletion K) x =
      algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)
        (algebraMap k (Work.SSGRoute.localFieldAt k A hA) x) := fun x => (hcompat' x).symm
  haveI hsepK : IsSepClosure ↥K Ω :=
    ⟨(inferInstance : IsSepClosure k Ω).sep_closed, inferInstance⟩
  -- the `K`-version of the compatibility of the place with the prime, used to build `θM`
  have hAqK := Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
  haveI : IsScalarTower k (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq (fun x => hcompat x)
  have hcont : Continuous
      (algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)) :=
    Work.LocalFields.completion_algebraMap_continuous (K := k) (L := ↥K)
      (Work.SSGRoute.primeUnder k A hA) q
  haveI : ContinuousSMul (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    continuousSMul_of_algebraMap _ _ hcont
  haveI : Module.Finite (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) := inferInstance
  haveI : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) := inferInstance
  haveI : IsGalois (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    Work.LocalFields.isGalois_completion (K := k) (L := ↥K) (Work.SSGRoute.primeUnder k A hA) q
  have hlin : ∀ c : Work.SSGRoute.localFieldAt k A hA,
      NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := ↥K) (K' := Ω) q A hAqK
          (algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) c) =
        algebraMap (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) c :=
    fun c => RingHom.congr_fun
      (Work.SSGRoute.adicCompletionToPlaceCompletion_comp k Ω K A hA q hAq hAqK hLies) c
  obtain ⟨θM, hθM⟩ :=
    Work.SSGRoute.exists_algHom_adicCompletion_adjoinPlaceCompletion k Ω K A hA q hAq hAqK
      hLies hlin
  -- the seam `Ω → M` is the *canonical* one, `e = adjoinSepEquiv`
  let e := NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
    (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
  let θ' : (q.adicCompletion K) →ₐ[Work.SSGRoute.localFieldAt k A hA]
      (Work.SSGRoute.localClosureAt k A hA) :=
    e.toAlgHom.comp θM
  let K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
      (Work.SSGRoute.localClosureAt k A hA) := θ'.fieldRange
  let ψ : ↥K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (q.adicCompletion K) :=
    θ'.equivFieldRange.symm
  haveI hfd : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K' :=
    LinearEquiv.finiteDimensional θ'.equivFieldRange.toLinearEquiv
  haveI hgal : IsGalois (Work.SSGRoute.localFieldAt k A hA) K' :=
    IsGalois.of_algEquiv θ'.equivFieldRange
  obtain ⟨eG, hiso, hpt⟩ :=
    Work.SSGRoute.localUnitsK_iso_intermediateField_pointwise k Ω K A hA q hLies K' ψ
  -- and `Φ` is the *canonical* homeomorphism `localGaloisEquiv`
  let Φ : ↥(SSGRoute.decomp k A) ≃*
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) :=
    NK.Mine.localGaloisEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
      (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
        (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA))
  have hΦ : IsHomeomorph (Φ : ↥(SSGRoute.decomp k A) →
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA)) :=
    Work.SSGRoute.isHomeomorph_localGaloisEquiv k Ω A hA
  have hψ : ∀ y : K,
      ((ψ.symm (algebraMap K (q.adicCompletion K) y) : ↥K') :
        Work.SSGRoute.localClosureAt k A hA) =
      e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A (algebraMap K Ω y)) := by
    intro y
    have h1 : ((ψ.symm (algebraMap K (q.adicCompletion K) y) : ↥K') :
        Work.SSGRoute.localClosureAt k A hA) =
        θ' (algebraMap K (q.adicCompletion K) y) :=
      AlgHom.equivFieldRange_apply_coe θ' (algebraMap K (q.adicCompletion K) y)
    rw [h1]
    show e (θM (algebraMap K (q.adicCompletion K) y)) =
      e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A (algebraMap K Ω y))
    rw [hθM y]
  have h4 : ∀ (σ : ↥(SSGRoute.decomp k A)) (x : K),
      (Φ σ) (ψ.symm (algebraMap K (q.adicCompletion K) x)) =
        ψ.symm (algebraMap K (q.adicCompletion K)
          ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x)) := by
    intro σ x
    rw [hψ x, hψ ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x)]
    exact Work.SSGRoute.localGaloisEquiv_adjoin_coInAdjoin_compat k Ω K A hA σ x
  -- the seam: `Φ` restricts to `σ` on all of `Ω`, not only on `K`
  have hseam : ∀ (σ : ↥(SSGRoute.decomp k A)) (y : Ω),
      (Φ σ) (e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
          (Work.SSGRoute.primeUnder k A hA) A y)) =
        e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
          (Work.SSGRoute.primeUnder k A hA) A ((σ : Ω ≃ₐ[k] Ω) y)) := by
    intro σ y
    exact Work.SSGRoute.localGaloisEquiv_coInAdjoin_compat_general k Ω A hA σ y
  exact ⟨K', hfd, hgal, ψ, eG, Φ,
    (e.toRingEquiv : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A) →+* Work.SSGRoute.localClosureAt k A hA),
    hΦ, hiso, hpt, h4, hψ, hseam⟩

end Work.SSGRoute.E1aClean
