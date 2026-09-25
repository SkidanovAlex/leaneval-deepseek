import Mathlib
import Submission.NK.ChebotarevGeneral.Defs
import Submission.NK.ChebotarevGeneral.Basic
import Submission.Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum

namespace NK.ChebotarevGeneral

open NumberField IsDedekindDomain
open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

section Helpers

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [FiniteDimensional K M]

/-- **The residue degree over the prime below.**  If `𝒬` lies over `𝔭` and the residue degree of
`𝒬` over the prime of `K` below it is one, then the residue degree of `𝒬` over `𝔭` is one. -/
lemma inertiaDeg'_eq_one_of_liesOver {𝒬 : NK.Chebotarev.PrimeIdeal M}
    {𝔭 : NK.Chebotarev.PrimeIdeal K} (h : 𝒬.asIdeal.LiesOver 𝔭.asIdeal)
    (hf : (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal = 1) :
    𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal = 1 := by
  rw [(Ideal.liesOver_iff 𝒬.asIdeal 𝔭.asIdeal).mp h]
  exact hf

/-- **Residue degree one implies equality of the absolute norms.**  If `𝒬` lies over `𝔭` and the
residue degree of `𝒬` over `𝔭` is one, then `N 𝒬 = N 𝔭`. -/
lemma absNorm_eq_of_inertiaDeg'_eq_one {𝒬 : NK.Chebotarev.PrimeIdeal M}
    {𝔭 : NK.Chebotarev.PrimeIdeal K} (h : 𝒬.asIdeal.LiesOver 𝔭.asIdeal)
    (hd : 𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal = 1) :
    (Ideal.absNorm 𝒬.asIdeal : ℝ) = (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
  haveI : 𝒬.asIdeal.LiesOver 𝔭.asIdeal := h
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver (S := NumberField.RingOfIntegers K)
    (R := NumberField.RingOfIntegers M) 𝒬.asIdeal 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot
  rw [hd, pow_one] at hn
  rw [hn]

/-- The sum of a constant over a finite type, in terms of `Nat.card`. -/
lemma tsum_const_eq_natCard_mul {α : Type*} [Finite α] (c : ℝ) :
    ∑' _ : α, c = (Nat.card α : ℝ) * c := by
  letI := Fintype.ofFinite α
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- **Only finitely many primes of `M` lie over a fixed prime of `K`.**  (Universe-polymorphic
version of `NK.ChebotarevGeneral.finite_setOf_liesOver`.) -/
lemma finite_setOf_liesOver' {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] (𝔭 : NK.Chebotarev.PrimeIdeal K) :
    {𝒬 : NK.Chebotarev.PrimeIdeal M | 𝒬.asIdeal.LiesOver 𝔭.asIdeal}.Finite := by
  have hfin : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers M)).Finite :=
    Commons.NumberTheory.NumberField.finite_primesOver 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot
  refine Set.Finite.of_finite_image (s := {𝒬 : NK.Chebotarev.PrimeIdeal M |
      𝒬.asIdeal.LiesOver 𝔭.asIdeal})
    (f := fun 𝒬 : NK.Chebotarev.PrimeIdeal M => 𝒬.asIdeal) ?_ ?_
  · exact hfin.subset (by
      rintro _ ⟨𝒬, h𝒬, rfl⟩
      exact ⟨inferInstance, h𝒬⟩)
  · intro 𝒬 _ 𝒬' _ h
    exact HeightOneSpectrum.ext h

end Helpers

/-- **Grouping a Dirichlet series over the primes of `M` by the prime of `K` below.**

If every prime `𝒬` of the set `S` has residue degree one over the prime of `K` below it, then the
partial Dirichlet series over `S` is the sum over the primes `𝔭` of `K` of the number of primes of
`S` above `𝔭` times `N𝔭^{-s}`. -/
theorem primeIdealZetaSum_eq_tsum_fibre {K M : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M]
    {S : Set (NK.Chebotarev.PrimeIdeal M)}
    (hS : ∀ 𝒬 ∈ S,
      (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal = 1)
    {s : ℝ} (hs : 1 < s) :
    NumberField.Set.primeIdealZetaSum S s =
      ∑' 𝔭 : NK.Chebotarev.PrimeIdeal K,
        (Nat.card {𝒬 : S // (𝒬 : NK.Chebotarev.PrimeIdeal M).asIdeal.LiesOver 𝔭.asIdeal} : ℝ) *
          (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  classical
  rw [NumberField.Set.primeIdealZetaSum_def]
  -- the series over `S` converges
  have hSsumm : Summable fun 𝒬 : S =>
      (Ideal.absNorm 𝒬.1.asIdeal : ℝ) ^ (-s) :=
    (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := M) hs).subtype S
  -- the partition of `S` by the prime of `K` below
  have hpart : ∀ x : S, ∃! 𝔭 : NK.Chebotarev.PrimeIdeal K,
      x.1.asIdeal.LiesOver 𝔭.asIdeal := by
    intro x
    refine ⟨HeightOneSpectrum.under (NumberField.RingOfIntegers K) x.1, ?_, ?_⟩
    · exact (Ideal.liesOver_iff x.1.asIdeal _).mpr
        (HeightOneSpectrum.under_asIdeal (NumberField.RingOfIntegers K) x.1)
    · intro 𝔭 h𝔭
      refine HeightOneSpectrum.ext ?_
      rw [(Ideal.liesOver_iff x.1.asIdeal 𝔭.asIdeal).mp h𝔭,
        HeightOneSpectrum.under_asIdeal (NumberField.RingOfIntegers K) x.1]
  -- summability of the family indexed by the disjoint union of the fibres
  have hSigma : Summable fun x : (Σ 𝔭 : NK.Chebotarev.PrimeIdeal K,
      ↥{𝒬 : S | 𝒬.1.asIdeal.LiesOver 𝔭.asIdeal}) =>
      (Ideal.absNorm x.2.1.1.asIdeal : ℝ) ^ (-s) :=
    (Equiv.summable_iff (Set.sigmaEquiv (fun 𝔭 : NK.Chebotarev.PrimeIdeal K =>
      {𝒬 : S | 𝒬.1.asIdeal.LiesOver 𝔭.asIdeal}) hpart)).mpr hSsumm
  calc ∑' 𝒬 : S, (Ideal.absNorm 𝒬.1.asIdeal : ℝ) ^ (-s)
      = ∑' x : (Σ 𝔭 : NK.Chebotarev.PrimeIdeal K,
            ↥{𝒬 : S | 𝒬.1.asIdeal.LiesOver 𝔭.asIdeal}),
          (Ideal.absNorm x.2.1.1.asIdeal : ℝ) ^ (-s) :=
        (Equiv.tsum_eq (Set.sigmaEquiv (fun 𝔭 : NK.Chebotarev.PrimeIdeal K =>
            {𝒬 : S | 𝒬.1.asIdeal.LiesOver 𝔭.asIdeal}) hpart)
          (fun 𝒬 : S => (Ideal.absNorm 𝒬.1.asIdeal : ℝ) ^ (-s))).symm
    _ = ∑' 𝔭 : NK.Chebotarev.PrimeIdeal K,
          ∑' 𝒬 : ↥{𝒬 : S | 𝒬.1.asIdeal.LiesOver 𝔭.asIdeal},
            (Ideal.absNorm 𝒬.1.1.asIdeal : ℝ) ^ (-s) :=
        hSigma.tsum_sigma
    _ = ∑' 𝔭 : NK.Chebotarev.PrimeIdeal K,
          (Nat.card {𝒬 : S // (𝒬 : NK.Chebotarev.PrimeIdeal M).asIdeal.LiesOver 𝔭.asIdeal} : ℝ) *
            (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
        refine tsum_congr fun 𝔭 => ?_
        -- the fibre is finite
        haveI hfin : Finite ↥{𝒬 : S | 𝒬.1.asIdeal.LiesOver 𝔭.asIdeal} := by
          haveI : Finite {𝔮 : NK.Chebotarev.PrimeIdeal M //
              𝔮.asIdeal.LiesOver 𝔭.asIdeal} :=
            (finite_setOf_liesOver' (K := K) (M := M) 𝔭).to_subtype
          exact Finite.of_injective
            (fun x : ↥{𝒬 : S | 𝒬.1.asIdeal.LiesOver 𝔭.asIdeal} =>
              (⟨(x.1 : NK.Chebotarev.PrimeIdeal M), x.2⟩ :
                {𝔮 : NK.Chebotarev.PrimeIdeal M // 𝔮.asIdeal.LiesOver 𝔭.asIdeal}))
            (fun x y h => Subtype.ext (Subtype.ext
              (congrArg (fun z : {𝔮 : NK.Chebotarev.PrimeIdeal M //
                  𝔮.asIdeal.LiesOver 𝔭.asIdeal} => (z.1 : NK.Chebotarev.PrimeIdeal M)) h)))
        -- each term of the fibre is the same
        have hterm : ∀ 𝒬 : ↥{𝒬 : S | 𝒬.1.asIdeal.LiesOver 𝔭.asIdeal},
            (Ideal.absNorm 𝒬.1.1.asIdeal : ℝ) ^ (-s)
              = (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
          intro 𝒬
          exact congrArg (fun t : ℝ => t ^ (-s))
            (absNorm_eq_of_inertiaDeg'_eq_one 𝒬.2
              (inertiaDeg'_eq_one_of_liesOver 𝒬.2 (hS _ 𝒬.1.2)))
        refine Eq.trans (tsum_congr hterm) ?_
        exact tsum_const_eq_natCard_mul _

end

end NK.ChebotarevGeneral
