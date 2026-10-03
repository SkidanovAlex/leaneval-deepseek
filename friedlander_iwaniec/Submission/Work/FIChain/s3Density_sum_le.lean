import Mathlib
import Submission.Work.FIChain.S3plusC_route_defs
import Submission.Work.FIChain.FIgtil_tau_div_sum_le
import Submission.Work.FIChain.FIgtil_prime_sum_loglog
import Submission.Work.FIChain.FIgtil_prime_div_sqrt_sum

namespace Work.FIChain

open Finset

noncomputable section

/-- **The sharp `g̃`-density sum of the `(2.4)`-counting.**  For `Y ≥ 2`,
`Σ_{n ≤ Y} g̃(n)·σ̃(n) ≤ C·log Y`, where `g̃ = Submission.ASP.FIgtil` and
`σ̃(n) = Work.FIChain.sigmaTilde n = ∏_{p | n}(1 + 1/√p)`.

(The weaker bound `C·(log Y)²` follows from the already-proved
`Work.FIChain.FIgtil_divisor_sigma_sum_le` since `τ(n) ≥ 1`; the *sharp* `log Y` above is what
the `(log)`-budget of the level sum needs.)

Route (standard Euler product, as in `Work.FIChain.sum_tauSq_gtil_le`): `g̃` vanishes off
squarefree `n` and is multiplicative, so the sum equals
`Σ_{ν squarefree ≤ Y} ∏_{p | ν}(g̃(p)·(1+1/√p)) ≤ ∏_{p ≤ Y}(1 + g̃(p)σ̃(p))
≤ exp(Σ_{p ≤ Y} g̃(p)σ̃(p))`, and `Σ_{p ≤ Y}g̃(p)σ̃(p) = Σ_{p≤Y}g̃(p) + Σ_{p≤Y}g̃(p)/√p
≤ loglog Y + K + K'` by `Work.FIChain.FIgtil_prime_sum_loglog` (module
`Submission.Work.FIChain.FIgtil_prime_sum_loglog`) and
`Work.FIChain.FIgtil_prime_div_sqrt_sum` (module
`Submission.Work.FIChain.FIgtil_prime_div_sqrt_sum`), so the product is `≤ e^{K+K'}·log Y`. -/
theorem s3Density_sum_le : ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ, 2 ≤ Y →
    ∑ n ∈ Finset.Icc 1 Y, Submission.ASP.FIgtil n * Work.FIChain.sigmaTilde n
      ≤ C * Real.log (Y : ℝ) := by
  obtain ⟨K1, hK1⟩ := FIgtil_prime_sum_loglog
  obtain ⟨K2, hK2⟩ := FIgtil_prime_div_sqrt_sum
  refine ⟨Real.exp (K1 + K2), Real.exp_pos _, fun Y hY => ?_⟩
  -- the local Euler factor `g̃(p)·(1 + 1/√p)`
  set w : ℕ → ℝ := fun p => Submission.ASP.FIgtil p * (1 + 1 / Real.sqrt (p : ℝ)) with hw
  have hw_nonneg : ∀ p, 0 ≤ w p := by
    intro p; rw [hw]
    have h1 : (0 : ℝ) ≤ Submission.ASP.FIgtil p := Submission.ASP.FIgtil_nonneg p
    have h2 : (0 : ℝ) ≤ 1 + 1 / Real.sqrt (p : ℝ) := by positivity
    positivity
  -- step 1: only the squarefree `n` contribute
  have hstep1 : ∑ n ∈ Finset.Icc 1 Y, Submission.ASP.FIgtil n * Work.FIChain.sigmaTilde n
      = ∑ n ∈ (Finset.Icc 1 Y).filter Squarefree,
          Submission.ASP.FIgtil n * Work.FIChain.sigmaTilde n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : Squarefree n
    · rw [if_pos h]
    · rw [if_neg h]; simp [Submission.ASP.FIgtil_eq_zero h]
  -- step 2: termwise Euler factorisation, then the squarefree Euler product
  have hstep2 : ∑ n ∈ (Finset.Icc 1 Y).filter Squarefree,
          Submission.ASP.FIgtil n * Work.FIChain.sigmaTilde n
      ≤ ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (1 + w p) := by
    calc ∑ n ∈ (Finset.Icc 1 Y).filter Squarefree,
            Submission.ASP.FIgtil n * Work.FIChain.sigmaTilde n
        = ∑ n ∈ (Finset.Icc 1 Y).filter Squarefree, ∏ p ∈ n.primeFactors, w p := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [Finset.mem_filter] at hn
          rw [Submission.ASP.FIgtil, if_pos hn.2, Work.FIChain.sigmaTilde, hw,
            ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun p hp => ?_
          show Submission.ASP.gtilVal Submission.ASP.FIg p * (1 + 1 / Real.sqrt (p : ℝ))
            = Submission.ASP.FIgtil p * (1 + 1 / Real.sqrt (p : ℝ))
          rw [Submission.ASP.FIgtil_prime (Nat.prime_of_mem_primeFactors hp)]
      _ ≤ ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (1 + w p) :=
          sum_sqfree_prod_le_prod Y w hw_nonneg
  -- step 3: `1 + y ≤ e^y`
  have hstep3 : ∏ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, (1 + w p)
      ≤ Real.exp (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, w p) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun p _ => by linarith [hw_nonneg p]) (fun p _ => ?_)
    have := Real.add_one_le_exp (w p); linarith
  -- step 4: the prime sums of `(1.9)` and of `g̃(p)/√p`
  have hwsum_eq : ∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, w p
      = (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, Submission.ASP.FIgtil p)
        + (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime,
            Submission.ASP.FIgtil p / Real.sqrt (p : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hw]; ring
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < Y))
  have hwsum_le : ∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, w p
      ≤ Real.log (Real.log (Y : ℝ)) + (K1 + K2) := by
    rw [hwsum_eq]
    have h1 := hK1 Y hY
    have h2 := hK2 Y
    linarith
  -- step 5: exponentiate
  refine le_trans (le_of_eq hstep1) (le_trans hstep2 (le_trans hstep3 ?_))
  calc Real.exp (∑ p ∈ (Finset.Icc 1 Y).filter Nat.Prime, w p)
      ≤ Real.exp (Real.log (Real.log (Y : ℝ)) + (K1 + K2)) := Real.exp_le_exp.mpr hwsum_le
    _ = Real.exp (K1 + K2) * Real.log (Y : ℝ) := by
        rw [Real.exp_add, Real.exp_log hlogY]; ring

end

end Work.FIChain
