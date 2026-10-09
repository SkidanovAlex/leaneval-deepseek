import Mathlib
import Submission.Work.SSGRoute.H9.swChainConjDefs
import Submission.Work.SSGRoute.EscapeCoreLib.correctionFromPrime
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.RamificationInertia.exists_smul_valuationSubringAtPrime_eq
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
import Submission.Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `𝔮`-count of a conjugate class at the conjugate place

Schmidt--Wingberg's escape normalisation is the congruence `v_Q(c) ≡ −1` for the escape element
`c ∈ Kˣ` at the escape prime `Q`.  The §4(b) chain of `H9.swChainValueH9` uses the same
normalisation not only at `Q` itself but at every *sibling* of `Q`, i.e. at the `K`-classes of the
places `galLift K σ • Q`, and for the *conjugate* class `c^σ = conjUnit (galLift K σ) c`.  This file
supplies the transport

  `count_{σ̃Q}(c^σ) = count_Q(c)`     (`σ̃ := galLift K σ`),

i.e. the divisor of a unit is Galois-equivariant.  The three ingredients are:

* `galLift K σ` restricts to `σ` on `↥K` (`galLift_spec`), hence
  `conjUnit (galLift K σ) b = σ b` on the nose;
* the prime of `𝓞 ↥K` below `σ̃ • Q` is the Galois transport `placeSmul σ` of the prime below `Q`
  (`oddPrime_galLift_smul`), because `σ̃` normalises `↥K` and acts on the valuation subrings of
  `↥K` by the pointwise action of `σ` (`comap_galLift_smul`);
* the `𝔮`-adic valuation is equivariant for this transport
  (`Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq`), and
  `count_spanSingleton_eq_neg_log` identifies the `count` of a principal fractional ideal with the
  logarithm of the valuation of its generator.

None of the three is specific to the escape primes; they hold for an arbitrary finite place `Q` and
an arbitrary unit `b`, which is the generality in which they are stated below.
-/

open scoped Pointwise

namespace Work.SSGRoute.H9

set_option linter.unusedSectionVars false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- **The `𝔮`-adic valuation is equivariant for the Galois transport of places.**  If `σ` is a
`k`-automorphism of the number field `K` and `𝔮` a height-one prime of `𝓞 K`, then the `σ`-image
`placeSmul σ 𝔮` of `𝔮` (the prime of `𝓞 K` obtained by pushing `𝔮` through the ring automorphism of
`𝓞 K` induced by `σ`) satisfies
`v_{σ𝔮}(σ x) = v_𝔮(x)` for every `x ∈ K`.

This is `Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq` in the AKLB setting
`𝓞 k ⊆ 𝓞 K ⊆ K`, `k ⊆ K`. -/
private theorem valuation_placeSmul (σ : K ≃ₐ[k] K)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) (x : ↥K) :
    (IsDedekindDomain.HeightOneSpectrum.valuation ↥K
      (Commons.NumberTheory.NumberField.Completion.placeSmul σ 𝔮) (σ x)) =
      (IsDedekindDomain.HeightOneSpectrum.valuation ↥K 𝔮) x :=
  Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
    (R := NumberField.RingOfIntegers ↥K) (K := ↥K)
    (galRestrict (NumberField.RingOfIntegers k) k (↥K) (NumberField.RingOfIntegers ↥K) σ :
      NumberField.RingOfIntegers ↥K ≃+* NumberField.RingOfIntegers ↥K)
    σ.toRingEquiv
    (fun r => (algebraMap_galRestrict_apply (NumberField.RingOfIntegers k) σ r).symm)
    𝔮 (Commons.NumberTheory.NumberField.Completion.placeSmul σ 𝔮)
    (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal σ 𝔮) x

/-- **`galLift K σ` acts on the valuation subrings of `↥K` through `σ`.**  The prime `𝓞 ↥K`-wise
trace of the place `galLift K σ • Q` is the `σ`-translate of the trace of `Q`. -/
private theorem comap_galLift_smul (σ : K ≃ₐ[k] K) (Q : ValuationSubring Ω) :
    (Work.SSGRoute.ZDataMup.galLift K σ • Q).comap (algebraMap ↥K Ω) =
      σ • (Q.comap (algebraMap ↥K Ω)) := by
  ext x
  -- `galLift K σ` restricts to `σ` on `↥K`, so it intertwines `algebraMap ↥K Ω` with the
  -- pointwise action of `σ⁻¹`.
  have hpt : (Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ • (algebraMap ↥K Ω x)
      = algebraMap ↥K Ω (σ⁻¹ • x) := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def]
    rw [← Work.SSGRoute.algebraMap_restrictNormalHom (K := K)
      ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹) x]
    congr 1
    rw [map_inv, Work.SSGRoute.ZDataMup.galLift_spec]
  rw [ValuationSubring.mem_comap]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rw [ValuationSubring.mem_comap, hpt]

/-- **The prime of `𝓞 ↥K` below `galLift K σ • Q` is the Galois transport of the prime below `Q`.**

`oddPrime (galLift K σ • Q) = placeSmul σ (oddPrime Q)`: both sides have the same trace on `↥K`, and
`valuationSubringAtPrime` is injective. -/
private theorem oddPrime_galLift_smul (σ : K ≃ₐ[k] K) (Q : ValuationSubring Ω)
    (hQ : SSGRoute.IsFinPlace k Q)
    (hQ' : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.galLift K σ • Q)) :
    Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (Work.SSGRoute.ZDataMup.galLift K σ • Q) hQ' =
      Commons.NumberTheory.NumberField.Completion.placeSmul σ
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Q hQ) := by
  apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
    (R := NumberField.RingOfIntegers ↥K) (K := ↥K)
  rw [← Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
    (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Q hQ)
    (Commons.NumberTheory.NumberField.Completion.placeSmul σ
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Q hQ)) σ
    (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal σ _)]
  rw [← Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := Q) hQ,
      ← Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K)
        (A := Work.SSGRoute.ZDataMup.galLift K σ • Q) hQ']
  exact comap_galLift_smul (K := K) σ Q

/-- **The `𝔮`-adic count of a conjugate class at the conjugate place.**  Conjugating the class `b ∈ Kˣ` by the lift `galLift K σ` and the place `Q` by the same element does not change the `𝔮`-count: the two `count` values agree.  This is the transport of Schmidt--Wingberg's escape normalisation `v_Q(b) ≡ −1` to the siblings of the escape primes, and it is what makes the local dictionary at a sibling usable. -/
theorem swCount_conjUnit {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (b : (↥K)ˣ) (σ : K ≃ₐ[k] K) (Q : ValuationSubring Ω) (hQ : SSGRoute.IsFinPlace k Q)
    (hQ' : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.galLift K σ • Q)) :
    FractionalIdeal.count ↥K
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) (Work.SSGRoute.ZDataMup.galLift K σ • Q) hQ')
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          ((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) b : (↥K)ˣ) : ↥K))
      = FractionalIdeal.count ↥K
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Q hQ)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (b : ↥K)) := by
  -- the conjugate class is the image of `b` under `σ`
  have hconj : ((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) b : (↥K)ˣ) : ↥K)
      = σ (b : ↥K) := by
    rw [Work.SSGRoute.H9.conjUnit, Units.coe_map, Work.SSGRoute.ZDataMup.galLift_spec]
    rfl
  rw [hconj, oddPrime_galLift_smul (K := K) σ Q hQ hQ']
  -- reduce both sides to the logarithm of the corresponding valuation
  rw [Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log (K := ↥K) _
        ((map_ne_zero σ).mpr (Units.ne_zero b)),
      Work.SSGRoute.EscapeCoreLib.count_spanSingleton_eq_neg_log (K := ↥K) _ (Units.ne_zero b)]
  -- the valuation of the conjugate at the conjugate place
  rw [valuation_placeSmul (K := K) σ (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Q hQ)
    (b : ↥K)]

end Work.SSGRoute.H9
