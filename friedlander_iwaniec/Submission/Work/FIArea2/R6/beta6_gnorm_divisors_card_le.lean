/-
# `FIArea2/R6/beta6_gnorm_divisors_card_le`

On the support of a round-6 coefficient, `τ(|z|²) ≤ 2^{log(2N)/log P}`: the support is free of
primes `≤ P` (`NoSmallPrimes`), so `P^{ω(|z|²)} ≤ |z|²`, hence
`ω(|z|²) ≤ log|z|²/log P ≤ log(2N)/log P`, and `|z|²` is squarefree, so `τ = 2^{ω}`.
-/
import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea3.lemma_2_2
import Submission.Work.FIArea2.R6.BetaFacts6

set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

/-- On the `β`-support, `τ(|z|²) ≤ 2^{log(2N)/log P}`. -/
theorem beta6_gnorm_divisors_card_le_logPz {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) :
    ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ (2 : ℝ) ^ (Real.log (2 * (Pa.N : ℝ)) / Real.log (Pa.Pz : ℝ)) := by
  set n : ℕ := Work.FIPlan.gnorm z with hn
  have hsq : Squarefree n := Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ hz
  have hns : Work.FITop4.NoSmallPrimes Pa z := Work.FITop4.IsBetaCoeff6.noSmallPrimes hβ hz
  obtain ⟨hNgt, hNle⟩ := Work.FIArea2.R6.IsBetaCoeff6.gnorm_bounds hβ hz
  have hn1 : 1 ≤ n := by
    have h1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
    have h2 : (1 : ℝ) ≤ (n : ℝ) := by rw [hn]; linarith
    exact_mod_cast h2
  have hPz1 : (1 : ℝ) < (Pa.Pz : ℝ) := by
    have : 1 < Pa.Pz := by have := Pa.hP2; omega
    exact_mod_cast this
  have hlogP : 0 < Real.log (Pa.Pz : ℝ) := Real.log_pos hPz1
  -- every prime factor of `n` exceeds `Pz`
  have hmem : ∀ p ∈ n.primeFactors, Pa.Pz < p := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    rw [hn] at hpd
    by_contra hle
    push_neg at hle
    exact hns p hpp (by omega) hpd
  -- `Pz ^ ω(n) ≤ n`
  have hprod : Pa.Pz ^ n.primeFactors.card ≤ n := by
    have h1 : ∏ _p ∈ n.primeFactors, Pa.Pz ≤ ∏ p ∈ n.primeFactors, p :=
      Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) (fun p hp => le_of_lt (hmem p hp))
    rw [Finset.prod_const, Nat.prod_primeFactors_of_squarefree hsq] at h1
    exact h1
  -- `ω(n) ≤ log n / log Pz`
  have hom : ((n.primeFactors.card : ℕ) : ℝ) ≤ Real.log (n : ℝ) / Real.log (Pa.Pz : ℝ) := by
    have hcast : ((Pa.Pz : ℝ)) ^ n.primeFactors.card ≤ (n : ℝ) := by exact_mod_cast hprod
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hlog : Real.log (((Pa.Pz : ℝ)) ^ n.primeFactors.card) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) hcast
    rw [Real.log_pow] at hlog
    rw [le_div_iff₀ hlogP]
    linarith [hlog]
  -- `τ(n) = 2^{ω(n)}`
  have htau : n.divisors.card = 2 ^ n.primeFactors.card :=
    Work.FIArea3.tau_card_of_squarefree hsq
  have hcast_nat : (((n.divisors.card : ℕ)) : ℝ) = (2 : ℝ) ^ n.primeFactors.card := by
    rw [htau]; push_cast; ring
  have hcastτ : (((n.divisors.card : ℕ)) : ℝ)
      = (2 : ℝ) ^ ((n.primeFactors.card : ℕ) : ℝ) := by
    rw [hcast_nat, Real.rpow_natCast]
  rw [hcastτ]
  -- `log n ≤ log (2N)`
  have hn2N : (n : ℝ) ≤ 2 * (Pa.N : ℝ) := by
    have hθ1 := theta_le_one6 Pa
    have hN0 : (0 : ℝ) ≤ (Pa.N : ℝ) := by linarith [Pa.hN1]
    nlinarith [hNle, hθ1, hN0]
  have hlog2N : Real.log (n : ℝ) ≤ Real.log (2 * (Pa.N : ℝ)) := by
    refine Real.log_le_log (by exact_mod_cast hn1) ?_
    rw [hn] at hn2N ⊢
    exact hn2N
  have hexp : ((n.primeFactors.card : ℕ) : ℝ)
      ≤ Real.log (2 * (Pa.N : ℝ)) / Real.log (Pa.Pz : ℝ) := by
    have h1 : Real.log (n : ℝ) / Real.log (Pa.Pz : ℝ)
        ≤ Real.log (2 * (Pa.N : ℝ)) / Real.log (Pa.Pz : ℝ) :=
      div_le_div_of_nonneg_right hlog2N hlogP.le
    linarith [hom, h1]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- On the `β`-support, `τ(|z|²) ≤ 2^{log(2N)/(loglog x)²}` (using `(loglog x)² ≤ log Pz`). -/
theorem beta6_gnorm_divisors_card_le {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) :
    ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
      ≤ (2 : ℝ) ^ (Real.log (2 * (Pa.N : ℝ))
          / (Real.log (Real.log (Pa.x : ℝ))) ^ (2 : ℕ)) := by
  have hbase := beta6_gnorm_divisors_card_le_logPz hβ hz
  have hPz1 : (1 : ℝ) < (Pa.Pz : ℝ) := by
    have : 1 < Pa.Pz := by have := Pa.hP2; omega
    exact_mod_cast this
  have hlogP : 0 < Real.log (Pa.Pz : ℝ) := Real.log_pos hPz1
  have hℓ0 : 0 < Real.log (Real.log (Pa.x : ℝ)) := by
    have hx1 : (1 : ℝ) < (Pa.x : ℝ) := by
      have : 1 < Pa.x := by have := Pa.hx; omega
      exact_mod_cast this
    have hlogx1 : 1 < Real.log (Pa.x : ℝ) := by
      have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
      have hA : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
      have hB : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) h3
      linarith
    exact Real.log_pos hlogx1
  have hsq0 : 0 < (Real.log (Real.log (Pa.x : ℝ))) ^ (2 : ℕ) := by positivity
  have hPzle : (Real.log (Real.log (Pa.x : ℝ))) ^ (2 : ℕ) ≤ Real.log (Pa.Pz : ℝ) := Pa.hPlo
  have hnum0 : 0 ≤ Real.log (2 * (Pa.N : ℝ)) := by
    refine Real.log_nonneg ?_
    have : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
    linarith
  have hexp : Real.log (2 * (Pa.N : ℝ)) / Real.log (Pa.Pz : ℝ)
      ≤ Real.log (2 * (Pa.N : ℝ)) / (Real.log (Real.log (Pa.x : ℝ))) ^ (2 : ℕ) :=
    div_le_div_of_nonneg_left hnum0 hsq0 hPzle
  exact le_trans hbase (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

end Work.FIArea2.R6
