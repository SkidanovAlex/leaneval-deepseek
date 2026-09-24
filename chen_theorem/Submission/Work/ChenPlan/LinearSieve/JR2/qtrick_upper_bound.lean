import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.JR2.q_trick_upper_core
import Submission.Work.ChenPlan.LinearSieve.JR2.sharp_gp
import Submission.Work.ChenPlan.LinearSieve.JR2.Qmod_mul_VfR
import Submission.Work.ChenPlan.LinearSieve.JR2.subSieve_SharpNorm

namespace Work.ChenPlan.LinearSieve.JR2

open Finset
open scoped BigOperators
open Work.NumberTheory.Chen.APSwitchUpper

set_option maxHeartbeats 800000

/-- **The `σ > 2` (Q-trick) upper bound.**  Under `LayerSharpBound 1000 (99/100)`, the `Q`-trick
(`q_trick_upper_core`, with `Q = Qmod A u₀`, `D'' = ⌊D/Q⌋`) together with the sharp-normalised `λ⁺`
main-term bound `sharp_gp` applied to the `P/Q` sub-sieve (whose `SharpNorm · z ε` comes from
`subSieve_SharpNorm`), the density factorisation `Qmod_mul_VfR`, and the `3^ω`-weighted remainder
comparison (`hDle : Q·D'' ≤ D`), give the `riUp` upper bound at the reduced level `D''`.

Suggested imports: `Submission.Work.ChenPlan.LinearSieve.JR2.Defs`,
`Submission.Work.ChenPlan.LinearSieve.JR2.q_trick_upper_core`,
`Submission.Work.ChenPlan.LinearSieve.JR2.sharp_gp`,
`Submission.Work.ChenPlan.LinearSieve.JR2.Qmod_mul_VfR`,
`Submission.Work.ChenPlan.LinearSieve.JR2.subSieve_SharpNorm`. -/
theorem qtrick_upper_bound (hL : Work.ChenPlan.LinearSieve.JR2.LayerSharpBound 1000 (99/100))
    (A : BoundingSieve) {K ε u₀ z D : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1/100) (hu₀ : 2 ≤ u₀) (hu₀z : u₀ ≤ z) (hz : 2 ≤ z)
    (hK : 0 ≤ K) (hKε : K ≤ ε * Real.log u₀) (hX : 0 ≤ A.totalMass)
    (hlinR : Submission.ChenPlan.IsLinearRange A z K)
    (hDle : ((⌊D / (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ)
        * (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀ : ℝ) ≤ D)
    (hD2 : 2 ≤ ((⌊D / (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ))
    (hs1 : 1 ≤ Real.log ((⌊D / (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) / Real.log z) :
    Work.ChenPlan.LinearSieve.siftedSumR A z ≤ A.totalMass * Work.ChenPlan.LinearSieve.VfR A z *
        (Work.NumberTheory.Chen.APSwitchUpper.riUp
            (Real.log ((⌊D / (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) / Real.log z)
         + ε * (1000 * 10100) * Work.NumberTheory.Chen.APSwitchUpper.errH
            (Real.log ((⌊D / (Work.ChenPlan.LinearSieve.JR2.Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) / Real.log z))
      + Submission.ChenPlan.remSum A D := by
  classical
  have hD' : (1 : ℝ) < ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) := by linarith
  have hcore := q_trick_upper_core A u₀ z (((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ)) hu₀ hu₀z hz hD'
  obtain ⟨hc1, hc2, hc3⟩ := hcore
  set Dn : ℝ := ((⌊D / (Qmod A u₀ : ℝ)⌋₊ : ℕ) : ℝ) with hDn
  set Rp : ℕ := Pz (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) z with hRp
  have hD1 : (1 : ℝ) ≤ Dn := by linarith
  -- the sharp normalisation of the `P/Q` sub-sieve
  have hSN : SharpNorm (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) z ε :=
    subSieve_SharpNorm A hK hε0 hu₀ hKε hlinR
  -- the sharp `λ⁺` main-term bound for the sub-sieve
  have hGp : RI.Gp (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) z Dn ≤
      VfR (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) z *
        (riUp (Real.log Dn / Real.log z) + ε * (1000 * 10100) * errH (Real.log Dn / Real.log z)) := by
    have h := sharp_gp 1000 (99/100) (by norm_num) (by norm_num) (by norm_num) hL
      (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) ε z Dn hε0 hε1 hz hD1 hSN hs1
    simpa [riUp] using h
  -- the density factor is nonnegative
  have hprod_nonneg : 0 ≤ ∏ p ∈ (Qmod A u₀).primeFactors, (1 - A.nu p) := by
    refine Finset.prod_nonneg (fun p hp => ?_)
    exact le_of_lt (VfR_factor_pos A (Nat.primeFactors_mono (Qmod_dvd A u₀) A.prodPrimes_ne_zero hp))
  -- split `multSum = ν·X + rem` termwise
  have hterm : ∀ q ∈ (Qmod A u₀).divisors, ∀ d ∈ Rp.divisors,
      ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
          * A.multSum (q * d)
      = ((((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
            * A.nu (q * d)) * A.totalMass
          + ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
            * A.rem (q * d)) := by
    intro q _ d _
    rw [BoundingSieve.multSum_eq_main_err]; ring
  have hdec : (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
        ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
          * A.multSum (q * d))
      = (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
            ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
              * A.nu (q * d)) * A.totalMass
        + ∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
            ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
              * A.rem (q * d) := by
    calc (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
            * A.multSum (q * d))
        = ∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
            ((((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
                * A.nu (q * d)) * A.totalMass
              + ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
                * A.rem (q * d)) :=
          Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun d hd => hterm q hq d hd))
      _ = (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
            ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
              * A.nu (q * d)) * A.totalMass
        + ∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
            ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
              * A.rem (q * d) := by
          simp only [Finset.sum_add_distrib, Finset.sum_mul]
  -- the main term: factorise the density and bound `Σ_d λ⁺ ν` by `Gp`
  have hd_sum : (∑ d ∈ Rp.divisors, lamPlus (A.prodPrimes / Qmod A u₀) Dn d * A.nu d)
      = RI.Gp (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) z Dn := by
    rw [← Gp_eq_sum_lamPlus (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) z Dn]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdRp : d ∣ Rp := (Nat.mem_divisors.mp hd).1
    have hdRp' : d ∣ Pz (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) z := hRp ▸ hdRp
    have hdP : d ∣ A.prodPrimes / Qmod A u₀ :=
      dvd_trans hdRp' (RI.Pz_dvd_prodPrimes (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) z)
    rw [lamPlus_eq_of_dvd hdP hdRp']
    rfl
  have hSν_le : (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
            ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
              * A.nu (q * d))
      ≤ (∏ p ∈ (Qmod A u₀).primeFactors, (1 - A.nu p)) *
        (VfR (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) z *
          (riUp (Real.log Dn / Real.log z) + ε * (1000 * 10100) * errH (Real.log Dn / Real.log z))) := by
    rw [hc2]
    refine mul_le_mul_of_nonneg_left ?_ hprod_nonneg
    rw [hd_sum]
    exact hGp
  -- the remainder: the `3^ω`-weighted bound
  have hSr_le : (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
            * A.rem (q * d))
      ≤ ∑ m ∈ (Pz A z).divisors.filter (fun m : ℕ => (m : ℝ) < (Qmod A u₀ : ℝ) * Dn),
          (3 : ℝ) ^ m.primeFactors.card * |A.rem m| := by
    calc (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
            * A.rem (q * d))
        ≤ ∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
            |((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d|
              * |A.rem (q * d)| := by
          refine Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun d _ => ?_))
          rw [← abs_mul]
          exact le_abs_self _
      _ ≤ ∑ m ∈ (Pz A z).divisors.filter (fun m : ℕ => (m : ℝ) < (Qmod A u₀ : ℝ) * Dn),
            (3 : ℝ) ^ m.primeFactors.card * |A.rem m| := hc3
  have hrem_le : (∑ m ∈ (Pz A z).divisors.filter (fun m : ℕ => (m : ℝ) < (Qmod A u₀ : ℝ) * Dn),
          (3 : ℝ) ^ m.primeFactors.card * |A.rem m|)
      ≤ Submission.ChenPlan.remSum A D := by
    rw [Submission.ChenPlan.remSum]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity)
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmdiv, hmlt⟩ := hm
    have hmP : m ∣ A.prodPrimes :=
      dvd_trans (Nat.mem_divisors.mp hmdiv).1 (RI.Pz_dvd_prodPrimes A z)
    have hmD : (m : ℝ) < D :=
      lt_of_lt_of_le hmlt (by rw [mul_comm]; exact hDle)
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hmP, A.prodPrimes_ne_zero⟩, hmD⟩
  -- assemble
  have hmain : (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
            * A.nu (q * d)) * A.totalMass
      ≤ A.totalMass * VfR A z *
          (riUp (Real.log Dn / Real.log z) + ε * (1000 * 10100) * errH (Real.log Dn / Real.log z)) := by
    refine le_trans (mul_le_mul_of_nonneg_right hSν_le hX) ?_
    rw [← mul_assoc (∏ p ∈ (Qmod A u₀).primeFactors, (1 - A.nu p))
        (VfR (subSieve A (Qmod A u₀) (Qmod_dvd A u₀)) z)
        (riUp (Real.log Dn / Real.log z) + ε * (1000 * 10100) * errH (Real.log Dn / Real.log z)),
      Qmod_mul_VfR A hu₀z]
    exact le_of_eq (by ring)
  calc Work.ChenPlan.LinearSieve.siftedSumR A z
      ≤ ∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
          ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
            * A.multSum (q * d) := hc1
    _ = (∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
            ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
              * A.nu (q * d)) * A.totalMass
        + ∑ q ∈ (Qmod A u₀).divisors, ∑ d ∈ Rp.divisors,
            ((ArithmeticFunction.moebius q : ℤ) : ℝ) * lamPlus (A.prodPrimes / Qmod A u₀) Dn d
              * A.rem (q * d) := hdec
    _ ≤ A.totalMass * Work.ChenPlan.LinearSieve.VfR A z *
          (riUp (Real.log Dn / Real.log z) + ε * (1000 * 10100) * errH (Real.log Dn / Real.log z))
        + Submission.ChenPlan.remSum A D := add_le_add hmain (le_trans hSr_le hrem_le)

end Work.ChenPlan.LinearSieve.JR2
