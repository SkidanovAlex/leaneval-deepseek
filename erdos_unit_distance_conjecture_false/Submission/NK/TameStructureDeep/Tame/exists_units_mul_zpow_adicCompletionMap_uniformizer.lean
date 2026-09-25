import Mathlib
import Submission.NK.TameStructureDeep.Tame.PowClassDeps

/-!
# Uniformisers of a local extension and the map of adic completions

Let `L / K` be a finite extension of number fields, `𝔭` a height-one prime of `𝓞 K`, `𝔮` a
height-one prime of `𝓞 L` lying over `𝔭`, and assume that `𝔮` is unramified over `𝔭`
(`𝔮.asIdeal.ramificationIdx (𝓞 K) = 1`).  Then the ring homomorphism of adic completions

`Commons.RingTheory.Henselian.adicCompletionMap 𝔭 𝔮 hlies : K_𝔭 →+* L_𝔮`

sends every uniformiser `π` of `K_𝔭` to a uniformiser of `L_𝔮`, and consequently every nonzero
element `x` of `L_𝔮` is `u * (adicCompletionMap 𝔭 𝔮 hlies π) ^ j` for a unit `u` of the ring of
integers and some `j : ℤ`.

The mathematics is the following.  In a discrete valuation ring the value of any irreducible
element is the same, namely `exp (-1)` in the value group `ℤᵐ⁰`: any two irreducibles generate the
same maximal ideal, hence are associates.  The formula
`Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow` gives
`v (adicCompletionMap 𝔭 𝔮 hlies x) = v x ^ e`, so with `e = 1` the image of the uniformiser `π`
again has value `exp (-1)`, and the general valuation identity
`Valuation.Integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap`
(`Ideal.span {x} = {y | v y ≤ v x}` in a valuation ring) shows that it generates the maximal
ideal, i.e. is irreducible.  Mathlib's
`IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible` then decomposes `x`.
-/

open scoped NumberField WithZero
open IsDedekindDomain

namespace NK.TameStructureDeep.Tame

theorem exists_units_mul_zpow_adicCompletionMap_uniformizer
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hlies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal)
    (he : 𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π)
    {x : 𝔮.adicCompletion L} (hx : x ≠ 0) :
    ∃ (j : ℤ) (u : (𝔮.adicCompletionIntegers L)ˣ),
      x = (u : 𝔮.adicCompletion L) *
        (Commons.RingTheory.Henselian.adicCompletionMap 𝔭 𝔮 hlies
          (π : 𝔭.adicCompletion K)) ^ j := by
  classical
  -- (A) All uniformisers of `𝔭` have the same value, namely `exp (-1)`.
  have hA : Valued.v (π : 𝔭.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    let ϖ : 𝔭.adicCompletionIntegers K :=
      Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers K) (K := K) 𝔭
    have hϖval : Valued.v (ϖ : 𝔭.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
      Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one (K := K) 𝔭
    have hϖirr : Irreducible ϖ :=
      Commons.RingTheory.Henselian.uniformizer_irreducible (K := K) 𝔭
    have hπirr : Irreducible π :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
    -- both generate the maximal ideal, hence are mutual divisors
    have hdiv1 : π ∣ ϖ := by
      have hmem : ϖ ∈ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) := by
        rw [IsLocalRing.mem_maximalIdeal]
        exact mem_nonunits_iff.mpr hϖirr.not_isUnit
      have h2 : ϖ ∈ Ideal.span {π} := hπ ▸ hmem
      rwa [Ideal.mem_span_singleton] at h2
    have hdiv2 : ϖ ∣ π := by
      have hmem : π ∈ IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) := by
        rw [IsLocalRing.mem_maximalIdeal]
        exact mem_nonunits_iff.mpr hπirr.not_isUnit
      have h2 : π ∈ Ideal.span {ϖ} :=
        (Commons.RingTheory.Henselian.maximalIdeal_eq_span_uniformizer
          (R := NumberField.RingOfIntegers K) (K := K) 𝔭) ▸ hmem
      rwa [Ideal.mem_span_singleton] at h2
    have hvK := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (R := NumberField.RingOfIntegers K) K 𝔭
    have hle1 : Valued.v (ϖ : 𝔭.adicCompletion K) ≤ Valued.v (π : 𝔭.adicCompletion K) :=
      (Valuation.Integers.le_iff_dvd hvK).mpr hdiv1
    have hle2 : Valued.v (π : 𝔭.adicCompletion K) ≤ Valued.v (ϖ : 𝔭.adicCompletion K) :=
      (Valuation.Integers.le_iff_dvd hvK).mpr hdiv2
    exact le_antisymm (hle2.trans_eq hϖval) (hϖval ▸ hle1)
  -- (B) The image of `π` in the completion of `L`.
  let π' : 𝔮.adicCompletionIntegers L :=
    ⟨Commons.RingTheory.Henselian.adicCompletionMap 𝔭 𝔮 hlies (π : 𝔭.adicCompletion K),
      Commons.RingTheory.Henselian.adicCompletionMap_mem_integers 𝔭 𝔮 hlies π.2⟩
  have hφval : Valued.v (Commons.RingTheory.Henselian.adicCompletionMap 𝔭 𝔮 hlies
      (π : 𝔭.adicCompletion K)) = WithZero.exp (-1 : ℤ) := by
    rw [Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow 𝔭 𝔮 hlies
      (π : 𝔭.adicCompletion K), hA, he, pow_one]
  have hπ'val : Valued.v (π' : 𝔮.adicCompletion L) = WithZero.exp (-1 : ℤ) := hφval
  -- (C) The image generates the maximal ideal of the ring of integers at `𝔮`.
  let ϖq : 𝔮.adicCompletionIntegers L :=
    Commons.RingTheory.Henselian.uniformizer (R := NumberField.RingOfIntegers L) (K := L) 𝔮
  have hϖqval : Valued.v (ϖq : 𝔮.adicCompletion L) = WithZero.exp (-1 : ℤ) :=
    Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one (K := L) 𝔮
  have hmaxq : IsLocalRing.maximalIdeal (𝔮.adicCompletionIntegers L) = Ideal.span {ϖq} :=
    Commons.RingTheory.Henselian.maximalIdeal_eq_span_uniformizer
      (R := NumberField.RingOfIntegers L) (K := L) 𝔮
  have hvL := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
    (R := NumberField.RingOfIntegers L) L 𝔮
  -- in a valuation ring, `Ideal.span {x} = {y | v y ≤ v x}`
  have hcoe1 : (Ideal.span {π'} : Set (𝔮.adicCompletionIntegers L)) =
      {y : 𝔮.adicCompletionIntegers L |
        Valued.v (y : 𝔮.adicCompletion L) ≤ Valued.v (π' : 𝔮.adicCompletion L)} :=
    Valuation.Integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap hvL π'
  have hcoe2 : (Ideal.span {ϖq} : Set (𝔮.adicCompletionIntegers L)) =
      {y : 𝔮.adicCompletionIntegers L |
        Valued.v (y : 𝔮.adicCompletion L) ≤ Valued.v (ϖq : 𝔮.adicCompletion L)} :=
    Valuation.Integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap hvL ϖq
  have hsets : (Ideal.span {π'} : Set (𝔮.adicCompletionIntegers L)) =
      (Ideal.span {ϖq} : Set (𝔮.adicCompletionIntegers L)) := by
    rw [hcoe1, hcoe2, hπ'val, hϖqval]
  have hspan : Ideal.span {π'} = IsLocalRing.maximalIdeal (𝔮.adicCompletionIntegers L) := by
    rw [hmaxq]
    exact SetLike.coe_set_eq.mp hsets
  have hπ'irr : Irreducible π' :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π').mpr hspan.symm
  -- (D) Every nonzero element of the completion is a unit times a power of a uniformiser.
  obtain ⟨j, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (R := 𝔮.adicCompletionIntegers L) (K := 𝔮.adicCompletion L) hπ'irr hx
  refine ⟨j, u, ?_⟩
  rw [hu]
  simp only [Units.smul_def, Algebra.smul_def, ValuationSubring.algebraMap_apply]
  rfl

end NK.TameStructureDeep.Tame
