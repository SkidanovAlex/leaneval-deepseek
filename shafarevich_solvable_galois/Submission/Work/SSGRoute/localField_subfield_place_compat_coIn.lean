import Mathlib
import Submission.Work.SSGRoute.localField_subfield_place_compat
import Submission.Work.SSGRoute.localGaloisEquiv_coInAdjoin_compat_general

/-!
# The `Ω`-compatibility clause of E7a's place glue, exported

`Work.SSGRoute.localField_subfield_place_compat` constructs the local data
`(K', ψ, eG, Φ)` of the place `A` and exports four clauses about it, but it does **not** export the
`Ω`-compatibility proved inside its own proof (the `hψ` block): the embedding of `K` into the local
closure `localClosureAt k A hA` given by the completion (`ψ.symm ∘ algebraMap K (q.adicCompletion K)`)
agrees with the embedding given by the place through `Ω` (`e ∘ coInAdjoin ∘ algebraMap K Ω`).

That clause is the coefficient-level half of the comparison square of the E1a lane: the values of an
element of `Hom_ℤ(R₁, Kˣ)` are units of `K`, and this is what identifies the global coefficient
`Kˣ ⊆ Ωˣ` with the local one `K_wˣ = K'ˣ ⊆ localClosureAtˣ`.  See
`PT/NOTE_e1aChainC_localComparison.md` §11.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 400000

/-- **The `Ω`-compatibility of E7a's place glue.**  There is a ring homomorphism
`e` from `adjoinPlaceCompletion` to the local closure such that, for every `y : K`, the image of `y`
in the local closure computed through the completion (`ψ.symm (algebraMap K (q.adicCompletion K) y)`)
equals `e` applied to `coInAdjoin (algebraMap K Ω y)`. -/
theorem localField_subfield_place_compat_coIn (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (hLies : q.asIdeal.LiesOver (Work.SSGRoute.primeUnder k A hA).asIdeal)
    (hAq' : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
        (Work.SSGRoute.primeUnder k A hA)) :
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA)
        (NK.NeukirchUchida.placeCompletion A) :=
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A hAq').toAlgebra
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
      (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies).toAlgebra
    (∀ x : k, algebraMap k (q.adicCompletion K) x =
      algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)
        (algebraMap k (Work.SSGRoute.localFieldAt k A hA) x)) →
    ∃ (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
          (Work.SSGRoute.localClosureAt k A hA))
      (ψ : ↥K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (q.adicCompletion K))
      (e : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω)
            (Work.SSGRoute.primeUnder k A hA) A) →+*
          Work.SSGRoute.localClosureAt k A hA),
      ∀ y : K, ((ψ.symm (algebraMap K (q.adicCompletion K) y) : ↥K') :
          Work.SSGRoute.localClosureAt k A hA)
        = e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
            (algebraMap K Ω y)) := by
  intro hcompat
  haveI hsepK : IsSepClosure ↥K Ω :=
    ⟨(inferInstance : IsSepClosure k Ω).sep_closed, inferInstance⟩
  have hAqK := place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies).toAlgebra
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
      (adicCompletionToPlaceCompletion_comp k Ω K A hA q hAq hAqK hLies) c
  obtain ⟨θM, hθM⟩ :=
    exists_algHom_adicCompletion_adjoinPlaceCompletion k Ω K A hA q hAq hAqK hLies hlin
  let e := NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
    (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
  let θ' : (q.adicCompletion K) →ₐ[Work.SSGRoute.localFieldAt k A hA]
      (Work.SSGRoute.localClosureAt k A hA) :=
    e.toAlgHom.comp θM
  let K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
      (Work.SSGRoute.localClosureAt k A hA) := θ'.fieldRange
  let ψ : ↥K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (q.adicCompletion K) :=
    θ'.equivFieldRange.symm
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
  exact ⟨K', ψ, (e.toRingEquiv : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω)
    (Work.SSGRoute.primeUnder k A hA) A) →+* Work.SSGRoute.localClosureAt k A hA), hψ⟩


/-- **Trap 2, resolved at the level of the place's own embedding.**  With the same data as
`localField_subfield_place_compat_coIn`, the automorphism `Φ σ` of the local closure acts on the
image of `Ω` under `e ∘ coInAdjoin` exactly as `σ` does.  This is the clause that the *coefficient
change* `Ωˣ → localClosureAtˣ` of the comparison square needs: it says that the abstract local
closure `SeparableClosure k_v` is a `D_A`-module under `Φ` in a way compatible with the place, i.e.
that the embedding of `Ω` determined by `A` is `Φ`-equivariant.  (It is *not* a statement about
`placeCompletionCoe`, whose codomain is the completion rather than the separable closure; §11.3's
"second trap" is exactly the gap between the two, and this clause is what closes it.) -/
theorem localField_subfield_place_compat_coIn_Omega (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (hLies : q.asIdeal.LiesOver (Work.SSGRoute.primeUnder k A hA).asIdeal)
    (hAq' : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
        (Work.SSGRoute.primeUnder k A hA)) :
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA)
        (NK.NeukirchUchida.placeCompletion A) :=
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
        (Work.SSGRoute.primeUnder k A hA) A hAq').toAlgebra
    letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
      (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies).toAlgebra
    (∀ x : k, algebraMap k (q.adicCompletion K) x =
      algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)
        (algebraMap k (Work.SSGRoute.localFieldAt k A hA) x)) →
    ∃ (K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
          (Work.SSGRoute.localClosureAt k A hA))
      (ψ : ↥K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (q.adicCompletion K))
      (e : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω)
            (Work.SSGRoute.primeUnder k A hA) A) →+*
          Work.SSGRoute.localClosureAt k A hA)
      (Φ : ↥(SSGRoute.decomp k A) ≃*
        (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA)),
      (∀ y : K, ((ψ.symm (algebraMap K (q.adicCompletion K) y) : ↥K') :
          Work.SSGRoute.localClosureAt k A hA)
        = e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
            (Work.SSGRoute.primeUnder k A hA) A (algebraMap K Ω y))) ∧
      (∀ (σ : ↥(SSGRoute.decomp k A)) (x : Ω),
          Φ σ (e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
              (Work.SSGRoute.primeUnder k A hA) A x))
            = e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
              (Work.SSGRoute.primeUnder k A hA) A ((σ : Ω ≃ₐ[k] Ω) x))) := by
  intro hcompat
  haveI hsepK : IsSepClosure ↥K Ω :=
    ⟨(inferInstance : IsSepClosure k Ω).sep_closed, inferInstance⟩
  have hAqK := place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (K := k) (K' := Ω)
      (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies).toAlgebra
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
      (adicCompletionToPlaceCompletion_comp k Ω K A hA q hAq hAqK hLies) c
  obtain ⟨θM, hθM⟩ :=
    exists_algHom_adicCompletion_adjoinPlaceCompletion k Ω K A hA q hAq hAqK hLies hlin
  let e := NK.Mine.adjoinSepEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
    (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
  let θ' : (q.adicCompletion K) →ₐ[Work.SSGRoute.localFieldAt k A hA]
      (Work.SSGRoute.localClosureAt k A hA) :=
    e.toAlgHom.comp θM
  let K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
      (Work.SSGRoute.localClosureAt k A hA) := θ'.fieldRange
  let ψ : ↥K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (q.adicCompletion K) :=
    θ'.equivFieldRange.symm
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
  let Φ : ↥(SSGRoute.decomp k A) ≃*
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) :=
    NK.Mine.localGaloisEquiv (K := k) (K' := Ω) (Work.SSGRoute.primeUnder k A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA) (fun z => rfl)
      (NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
        (Work.SSGRoute.primeUnder k A hA) A (Submission.NeukirchUchida.primeOf_spec A hA))
  have hOmega : ∀ (σ : ↥(SSGRoute.decomp k A)) (x : Ω),
      Φ σ (e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
          (Work.SSGRoute.primeUnder k A hA) A x))
        = e (NK.NeukirchUchida.coInAdjoin (K := k) (K' := Ω)
          (Work.SSGRoute.primeUnder k A hA) A ((σ : Ω ≃ₐ[k] Ω) x)) := by
    intro σ x
    exact localGaloisEquiv_coInAdjoin_compat_general k Ω A hA σ x
  exact ⟨K', ψ, (e.toRingEquiv : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω)
    (Work.SSGRoute.primeUnder k A hA) A) →+* Work.SSGRoute.localClosureAt k A hA), Φ, hψ, hOmega⟩

end Work.SSGRoute
