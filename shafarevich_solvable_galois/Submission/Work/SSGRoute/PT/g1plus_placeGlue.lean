import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.e1aBetaCan_hAq_decomp_map
import Submission.Work.SSGRoute.decompK_restrict_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute.PT

/-!
# Gluing the place of `Ω` with the place of a subfield

Let `k ⊆ K ⊆ L ⊆ Ω` be a tower of number fields inside an algebraic closure `Ω` of `k`, and let
`A` be a valuation subring of `Ω` whose restriction to `k` is a finite place.  Suppose the induced
prime of `𝓞 K` (resp. `𝓞 L`) is described by the valuation of `A`:

`x ∈ q ↔ v_A(x) < 1`, `x ∈ w ↔ v_A(x) < 1`.

Then

* the place `ofFinite w` of `L` lies over the place `ofFinite q` of `K`, and
* restriction of automorphisms `Gal(L/k) → Gal(K/k)` maps the decomposition group of `ofFinite w`
  into (in fact onto) the decomposition group of `ofFinite q`.

The second clause is the already-proved general fact `Work.SSGRoute.decompK_restrict_exists`; the
mathematical content here is the first clause, i.e. that the two valuation descriptions are
compatible: for `x : 𝓞 K` one has `v_A(ι x) < 1 ↔ v_A(x) < 1` because the canonical map
`𝓞 K → 𝓞 L` is the restriction of `K → L → Ω`.
-/

/-- **The `𝓞`-level algebra map is compatible with the field-level inclusion into `Ω`.**  For
`x` in the ring of integers of `K`, the image of `x` in the ring of integers of `L` has the same
image in `Ω` as `x` itself. -/
theorem placeGlue_ringOfIntegers_coe {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) [Algebra ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (x : NumberField.RingOfIntegers ↥K) :
    (((algebraMap (NumberField.RingOfIntegers ↥K) (NumberField.RingOfIntegers ↥L) x : ↥L) : Ω))
      = ((x : ↥K) : Ω) := by
  have h1 : ((algebraMap (NumberField.RingOfIntegers ↥K) (NumberField.RingOfIntegers ↥L) x : ↥L))
      = algebraMap (NumberField.RingOfIntegers ↥K) ↥L x := rfl
  rw [h1, IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ↥K) ↥K ↥L]
  exact (IsScalarTower.algebraMap_apply ↥K ↥L Ω (x : ↥K)).symm

/-- **The prime of `𝓞 K` below the prime of `𝓞 L` cut out by the same valuation subring.**  If the
ideals `q` and `w` are both described by the inequalities `v_A(-) < 1`, then `w` lies over `q`. -/
theorem placeGlue_liesOver_of_valuation {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K L : IntermediateField k Ω) [Algebra ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hAw : ∀ x : NumberField.RingOfIntegers ↥L,
      x ∈ w.asIdeal ↔ A.valuation (((x : ↥L) : Ω)) < 1) :
    w.asIdeal.LiesOver q.asIdeal := by
  refine Ideal.LiesOver.mk ?_
  ext x
  rw [Ideal.mem_under, hAq x, hAw (algebraMap (NumberField.RingOfIntegers ↥K)
    (NumberField.RingOfIntegers ↥L) x), placeGlue_ringOfIntegers_coe K L x]

theorem g1plus_placeGlue (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L] (hKL : K ≤ L)
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K, x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hAw : ∀ x : NumberField.RingOfIntegers ↥L, x ∈ w.asIdeal ↔ A.valuation (((x : ↥L) : Ω)) < 1) :
    NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite w) (NK.GlobalCFT.Place.ofFinite q) ∧
    ∃ f : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
        ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)),
      ∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
        ((f σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) : ↥K ≃ₐ[k] ↥K)
          = SSGRoute.PTExt.galRes k ↥K ↥L (σ : ↥L ≃ₐ[k] ↥L) := by
  haveI : FiniteDimensional ↥K ↥L := FiniteDimensional.right k ↥K ↥L
  have hlies : w.asIdeal.LiesOver q.asIdeal :=
    placeGlue_liesOver_of_valuation K L A q hAq w hAw
  have hPlace : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite w)
      (NK.GlobalCFT.Place.ofFinite q) :=
    NK.GlobalCFT.Place.liesOver_ofFinite hlies
  refine ⟨hPlace, ?_⟩
  exact Work.SSGRoute.decompK_restrict_exists k ↥K ↥L
    (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite w) hPlace

end Work.SSGRoute.PT
