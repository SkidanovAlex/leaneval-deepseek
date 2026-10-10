import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.PT.exists_place_under_isFinPlace
import Submission.Work.SSGRoute.decompK_restrict_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Gluing a place of `Ω` down to a tower `k ⊆ K ⊆ L`

Let `k` be a number field with algebraic closure `Ω`, let `K ⊆ L ⊆ Ω` be finite Galois intermediate
fields, and let `A` be a *finite* place of `Ω` over `k` (i.e. `A.comap (algebraMap k Ω) ≠ ⊤`).

The place of `K` cut out by `A` is the nonzero prime `q` of `𝓞 K` characterised by
`x ∈ q ↔ v_A(x : Ω) < 1`, and similarly the place of `L` is the prime `w` of `𝓞 L`.  The two
pieces of `place_glue_level` are then:

* `w.asIdeal.LiesOver q.asIdeal` (equivalently `Place.LiesOver (ofFinite w) (ofFinite q)`): the
  primes are the traces of *the same* valuation `v_A`, so restricting along `K → L` recovers the
  prime of `K`.  The only input is the compatibility of the structure maps
  `𝓞 K → 𝓞 L → L → Ω` and `𝓞 K → K → Ω`, which is `algebraMap_ringOfIntegers_coe_compat` below;
* the restriction homomorphism `decompK w →* decompK q`, which is
  `Work.SSGRoute.decompK_restrict_exists` applied to the lying-over relation just established.
-/

namespace Work.SSGRoute.PT

/-- **Compatibility of the structure maps on the rings of integers.**

For a tower `K ⊆ L ⊆ Ω` of intermediate fields (with the algebra structure `K → L` compatible with
the two inclusions into `Ω`), the two ways of sending `x ∈ 𝓞 K` to `Ω` — through `𝓞 L → L → Ω`
and through `K → Ω` — agree.

This is the `IsScalarTower` statement `algebraMap K Ω ∘ algebraMap K L = algebraMap L Ω ∘
algebraMap 𝓞K 𝓞L` read on the level of the rings of integers. -/
theorem algebraMap_ringOfIntegers_coe_compat {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) [Algebra ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (x : NumberField.RingOfIntegers ↥K) :
    (((algebraMap (NumberField.RingOfIntegers ↥K) (NumberField.RingOfIntegers ↥L) x :
        NumberField.RingOfIntegers ↥L) : ↥L) : Ω) = ((x : ↥K) : Ω) := by
  -- Both sides are `algebraMap 𝓞K ↥L x`: the left one by the `IsScalarTower` of `𝓞K ⊆ 𝓞L ⊆ L`,
  -- the right one by the `IsScalarTower` of `𝓞K ⊆ K ⊆ L`.
  have hkey : ((algebraMap (NumberField.RingOfIntegers ↥K) (NumberField.RingOfIntegers ↥L) x :
        NumberField.RingOfIntegers ↥L) : ↥L) = algebraMap ↥K ↥L (x : ↥K) := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap]
    rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥K)
      (NumberField.RingOfIntegers ↥L) ↥L]
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap]
    rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥K) ↥K ↥L]
  rw [hkey, ← IntermediateField.algebraMap_apply L (algebraMap ↥K ↥L (x : ↥K)),
    ← IntermediateField.algebraMap_apply K (x : ↥K)]
  rw [← IsScalarTower.algebraMap_apply ↥K ↥L Ω]

/-- **The primes of `𝓞 K` and `𝓞 L` cut out by the same place of `Ω` lie over each other.**

If `q` is the prime of `𝓞 K` and `w` the prime of `𝓞 L` defined by the same valuation
`A.valuation` of `Ω` (`hAq`, `hAw`), then `w.asIdeal.LiesOver q.asIdeal`, i.e. `q.asIdeal` is the
trace of `w.asIdeal` along `𝓞 K → 𝓞 L`. -/
theorem asIdeal_liesOver_of_valuation_lt_one {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) [Algebra ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hAw : ∀ y : NumberField.RingOfIntegers ↥L,
      y ∈ w.asIdeal ↔ A.valuation (((y : ↥L) : Ω)) < 1) :
    w.asIdeal.LiesOver q.asIdeal := by
  refine Ideal.LiesOver.mk (Ideal.ext fun x => ?_)
  rw [Ideal.mem_under, hAq x,
    hAw (algebraMap (NumberField.RingOfIntegers ↥K) (NumberField.RingOfIntegers ↥L) x),
    algebraMap_ringOfIntegers_coe_compat K L x]

theorem place_glue_level (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] [FiniteDimensional k L] [IsGalois k L] [NumberField L] (hKL : K ≤ L)
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hAw : ∀ y : NumberField.RingOfIntegers L, y ∈ w.asIdeal ↔ A.valuation (((y : L) : Ω)) < 1) :
    NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite w) (NK.GlobalCFT.Place.ofFinite q) ∧
    ∃ f : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
        ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)),
      ∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
        ((f σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) :
            ↥K ≃ₐ[k] ↥K) = SSGRoute.PTExt.galRes k (↥K) (↥L) (σ : ↥L ≃ₐ[k] ↥L) := by
  -- Both primes are the trace of the same place `A`, so `w` lies over `q`.
  have hlies : w.asIdeal.LiesOver q.asIdeal :=
    asIdeal_liesOver_of_valuation_lt_one K L A q hAq w hAw
  refine ⟨NK.GlobalCFT.Place.liesOver_ofFinite hlies, ?_⟩
  -- The restriction `Gal(L/k) →* Gal(K/k)` maps the decomposition group of `w` into the one
  -- of `q` whenever `w` lies over `q`: `Work.SSGRoute.decompK_restrict_exists`.
  obtain ⟨f, hf⟩ := Work.SSGRoute.decompK_restrict_exists k ↥K ↥L
    (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite w)
    (NK.GlobalCFT.Place.liesOver_ofFinite hlies)
  exact ⟨f, hf⟩

end Work.SSGRoute.PT
