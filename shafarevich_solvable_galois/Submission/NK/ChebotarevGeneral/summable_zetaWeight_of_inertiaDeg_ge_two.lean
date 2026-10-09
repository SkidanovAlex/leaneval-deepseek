import Mathlib
import Submission.NK.ChebotarevGeneral.Defs
import Submission.NK.HeckeL.Nonvanishing.primeFiber
import Submission.Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum
import Submission.Commons.NumberTheory.NumberField.ncard_primesOver_le_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ChebotarevGeneral

open NumberField IsDedekindDomain
open scoped BigOperators

set_option linter.style.haveILetI false

noncomputable section

open NK.HeckeL.Nonvanishing

/-- **The primes of residue degree `≥ 2` contribute a convergent Dirichlet series.**  For number
fields `K ⊆ M`, the sum of `N𝒬^{-s}` over the primes `𝒬` of `M` of residue degree at least `2` over
`K` converges for `s > 1/2`; in particular it is bounded as `s → 1⁺`. -/
theorem summable_zetaWeight_of_inertiaDeg_ge_two {K M : Type*} [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] [FiniteDimensional K M] {s : ℝ} (hs : (1 : ℝ) / 2 < s) :
    Summable (fun 𝒬 : NK.Chebotarev.PrimeIdeal M =>
      if 2 ≤ (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal
        then ((Ideal.absNorm 𝒬.asIdeal : ℝ) ^ (-s)) else 0) := by
  classical
  have h2s : (1 : ℝ) < 2 * s := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  -- The dominating function: the norm of the prime of `K` below `𝒬`, raised to `-2s`.
  set W : NK.Chebotarev.PrimeIdeal K → ℝ :=
    fun 𝔭 => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 * s)) with hW
  have hWsum : Summable W := by
    rw [hW]
    exact Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) h2s
  -- The fibre of the primes of `M` over a fixed prime of `K` is finite, of cardinality at most
  -- the degree `[M : K]`.
  have hcard_le : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K,
      (Fintype.card (primesOverPrime K M 𝔭) : ℝ) ≤ (Module.finrank K M : ℝ) := by
    intro 𝔭
    have h1 : Fintype.card (primesOverPrime K M 𝔭) ≤ Module.finrank K M := by
      rw [← Nat.card_eq_fintype_card, NK.HeckeL.Nonvanishing.natCard_primesOverPrime,
        Set.fintypeCard_eq_ncard]
      exact Commons.NumberTheory.NumberField.ncard_primesOver_le_finrank 𝔭
    exact_mod_cast h1
  -- Summability of the fibre-indexed family.
  have hsigma : Summable (fun x : (Σ 𝔭 : NK.Chebotarev.PrimeIdeal K,
        primesOverPrime K M 𝔭) => W x.1) := by
    refine (summable_sigma_of_nonneg (f := fun x : (Σ 𝔭 : NK.Chebotarev.PrimeIdeal K,
        primesOverPrime K M 𝔭) => W x.1)
        (fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _)).2 ⟨?_, ?_⟩
    · intro 𝔭
      exact Summable.of_finite
    · have hconst : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K,
          (∑' _y : primesOverPrime K M 𝔭, W 𝔭)
            = (Fintype.card (primesOverPrime K M 𝔭) : ℝ) * W 𝔭 := by
        intro 𝔭
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp_rw [hconst]
      refine Summable.of_nonneg_of_le (f := fun 𝔭 : NK.Chebotarev.PrimeIdeal K =>
            (Module.finrank K M : ℝ) * W 𝔭) (fun 𝔭 => ?_) (fun 𝔭 => ?_) ?_
      · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · exact mul_le_mul_of_nonneg_right (hcard_le 𝔭) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · exact hWsum.mul_left _
  -- Transport along the bijection between the primes of `M` and the disjoint union, over the
  -- primes of `K`, of the fibres.
  have hsumM : Summable (fun 𝒬 : NK.Chebotarev.PrimeIdeal M => W (underPrime (K := K) 𝒬)) := by
    refine (Equiv.summable_iff (Equiv.sigmaFiberEquiv (underPrime (K := K) :
      NK.Chebotarev.PrimeIdeal M → NK.Chebotarev.PrimeIdeal K))).mp ?_
    refine hsigma.congr (fun x => ?_)
    simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, x.2.2]
  -- Comparison: the terms of residue degree `≥ 2` are dominated by `W` of the prime below.
  refine Summable.of_nonneg_of_le (f := fun 𝒬 : NK.Chebotarev.PrimeIdeal M =>
      W (underPrime (K := K) 𝒬)) (fun 𝒬 => ?_) (fun 𝒬 => ?_) hsumM
  · split_ifs with h
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · exact le_refl 0
  · by_cases h : 2 ≤ (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal
    · rw [if_pos h]
      have hlies : 𝒬.asIdeal.LiesOver (underPrime (K := K) 𝒬).asIdeal :=
        underPrime_liesOver 𝒬
      haveI : 𝒬.asIdeal.LiesOver (underPrime (K := K) 𝒬).asIdeal := hlies
      have hnorm := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver (S := 𝓞 K) (R := 𝓞 M)
        𝒬.asIdeal (underPrime (K := K) 𝒬).asIdeal
        (underPrime (K := K) 𝒬).isPrime (underPrime (K := K) 𝒬).ne_bot
      have hf : 2 ≤ (underPrime (K := K) 𝒬).asIdeal.inertiaDeg' 𝒬.asIdeal := h
      rw [hnorm]
      push_cast
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      apply Real.rpow_le_rpow_of_exponent_le
      · have hne : Ideal.absNorm (underPrime (K := K) 𝒬).asIdeal ≠ 0 := by
          intro h0
          exact (underPrime (K := K) 𝒬).ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hne)
      · have : ((underPrime (K := K) 𝒬).asIdeal.inertiaDeg' 𝒬.asIdeal : ℝ) ≥ 2 := by
          exact_mod_cast hf
        nlinarith
    · rw [if_neg h]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _

end

end NK.ChebotarevGeneral
