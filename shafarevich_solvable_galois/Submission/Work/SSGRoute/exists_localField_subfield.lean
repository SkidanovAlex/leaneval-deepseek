import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.E7aAux
import Submission.Work.SSGRoute.isUnit_natCast_of_not_dvd_resCharAt
import Submission.Work.LocalFields.finrank_completion_eq_card_decompositionGroup
import Submission.Work.LocalFields.completion_algebraMap_continuous
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- **Place glue, first step: the completion `K_w` is an intermediate field of a separable closure
of `k_v`.**

`k` a number field, `Ω` a separable closure, `K/k` finite Galois, `A` a *finite* place of `Ω`, and
`q` a finite place of `K` whose prime is the one below `A` (`hAq` is exactly the correspondence
`x ∈ q ↔ v_A(x) < 1` on `𝒪_K`).  Put `L₀ := Work.SSGRoute.localFieldAt k A hA` (the `A`-adic
completion `k_v` of `k`) and `κ̄ := Work.SSGRoute.localClosureAt k A hA = SeparableClosure L₀`.

Then `K_w = q.adicCompletion K` is an `L₀`-algebra (the structure comes from
`Commons.RingTheory.Henselian.adicCompletionMap`; there is no library instance, so it is a
hypothesis, and `hcompat` records that it extends `algebraMap k`), and there is an intermediate
field `K' ⊆ κ̄` over `L₀` with `FiniteDimensional L₀ K'`, `IsGalois L₀ K'` and
`Nonempty (↥K' ≃ₐ[L₀] K_w)`.

This is the field-theoretic core of the E7a place glue (`K_w/k_v` is finite Galois because `K/k` is
and `q` lies over `A`'s prime; `L₀` has characteristic `0` and `κ̄` is a separable closure of `L₀`,
so any finite separable `L₀`-extension embeds into `κ̄`).  Subsequent glue steps only transport
`K_wˣ`, the group `Gal(K_w/L₀) ≅ ↥(decompK (Place.ofFinite q))` and the copy of `ζ`. -/
theorem exists_localField_subfield (k : Type) (Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    [Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)]
    (hcompat : ∀ x : k, algebraMap k (q.adicCompletion K) x =
      algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)
        (algebraMap k (Work.SSGRoute.localFieldAt k A hA) x)) :
    ∃ K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
        (Work.SSGRoute.localClosureAt k A hA),
      FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K' ∧
      IsGalois (Work.SSGRoute.localFieldAt k A hA) K' ∧
      Nonempty (↥K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (q.adicCompletion K)) := by
  -- **(1) `q` lies over the prime `v` of `k` cut out by `A`**, which is `hAq` transported through
  -- `valuation_lt_one_iff_mem_primeOf_of_numberField` (the identification of membership in
  -- `primeOf A hA` with the inequality `A.valuation · < 1` on `𝓞 k`).
  have hlies : q.asIdeal.LiesOver (Submission.NeukirchUchida.primeOf A hA).asIdeal := by
    refine Ideal.LiesOver.mk ?_
    ext x
    rw [Ideal.mem_comap, hAq,
      ← valuation_lt_one_iff_mem_primeOf_of_numberField k Ω A hA x]
    exact Iff.rfl
  -- `hcompat` is exactly the scalar-tower condition `k ⊆ k_v ⊆ K_w`.
  haveI : IsScalarTower k (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq (fun x => hcompat x)
  -- **(2) the structure map `k_v → K_w` is continuous** (rigidity of local fields).
  have hcont : Continuous (algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)) :=
    Work.LocalFields.completion_algebraMap_continuous (K := k) (L := ↥K)
      (Submission.NeukirchUchida.primeOf A hA) q
  haveI : ContinuousSMul (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    continuousSMul_of_algebraMap _ _ hcont
  -- **(3) `K_w` is finite dimensional and Galois over `k_v`** (the local fundamental identity
  -- for the module structure; `isGalois_completion` for Galois-ness).
  haveI : Module.Finite (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) := inferInstance
  haveI : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) := inferInstance
  haveI hgal : IsGalois (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    Work.LocalFields.isGalois_completion (K := k) (L := ↥K)
      (Submission.NeukirchUchida.primeOf A hA) q
  haveI : Algebra.IsSeparable (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    hgal.to_isSeparable
  -- **(4) embed the finite separable extension `K_w/k_v` into the separable closure `κ̄`.**
  let φ : (q.adicCompletion K) →ₐ[Work.SSGRoute.localFieldAt k A hA]
      (Work.SSGRoute.localClosureAt k A hA) := IsSepClosed.lift
  have hφinj : Function.Injective φ :=
    RingHom.injective (φ : (q.adicCompletion K) →+* Work.SSGRoute.localClosureAt k A hA)
  let K' : IntermediateField (Work.SSGRoute.localFieldAt k A hA)
      (Work.SSGRoute.localClosureAt k A hA) := φ.fieldRange
  have he : (q.adicCompletion K) ≃ₐ[Work.SSGRoute.localFieldAt k A hA] (↥K' : Type _) :=
    AlgEquiv.ofInjective φ hφinj
  exact ⟨K', LinearEquiv.finiteDimensional he.toLinearEquiv,
    IsGalois.of_algEquiv he, ⟨he.symm⟩⟩


end Work.SSGRoute
