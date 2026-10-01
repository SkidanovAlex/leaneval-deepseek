import Mathlib
import Submission.Commons.NumberTheory.Nat.pow_omega_le_const_mul_rpow
import Submission.Work.LinnikAreas.prod_le_prod_Icc_of_card
import Submission.Work.LinnikAreas.prod_Icc_two_one_add_rpow_le_exp

namespace Work.LinnikAreas

open Finset

theorem primeFactors_prod_one_add_rpow_le (q : ℕ) (hq : 3 ≤ q) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-σ)) ≤ Real.exp ((Real.log q) ^ (3 / 4 : ℝ)) := by
  -- Step 1: since `σ ≥ 1/2` and `p ≥ 1`, we have `p^{-σ} ≤ p^{-1/2}`.
  have hstep1 : ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-σ))
      ≤ ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-(1/2 : ℝ))) := by
    apply Finset.prod_le_prod₀
    · intro p hp
      have : (0 : ℝ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_nonneg (by positivity) _
      linarith
    · intro p hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
      have hle : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-(1/2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      linarith
  -- `q ≥ 3` gives at least one prime factor.
  have hcard1 : 1 ≤ q.primeFactors.card := by
    have hq0 : q ≠ 0 := by omega
    have hpq : (Nat.minFac q).Prime := Nat.minFac_prime (by omega : q ≠ 1)
    have hmem : Nat.minFac q ∈ q.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpq, Nat.minFac_dvd q, hq0⟩
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  -- Step 2: the product over the prime factors is dominated by the product over
  -- the `ω(q)` smallest integers `≥ 2`.
  have hstep2 : ∏ p ∈ q.primeFactors, (1 + (p : ℝ) ^ (-(1/2 : ℝ)))
      ≤ ∏ j ∈ Finset.Icc 2 (q.primeFactors.card + 1), (1 + (j : ℝ) ^ (-(1/2 : ℝ))) :=
    prod_le_prod_Icc_of_card
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      (fun t => 1 + (t : ℝ) ^ (-(1/2 : ℝ)))
      (fun t => by positivity)
      (fun a b _ hab => by
        have ha' : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
        have hle : (b : ℝ) ^ (-(1/2 : ℝ)) ≤ (a : ℝ) ^ (-(1/2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos ha' (by exact_mod_cast hab) (by norm_num)
        linarith)
  -- Step 3: the analytic cores inequality over the integers `2 .. ω(q)+1`.
  have hstep3 : ∏ j ∈ Finset.Icc 2 (q.primeFactors.card + 1), (1 + (j : ℝ) ^ (-(1/2 : ℝ)))
      ≤ Real.exp ((Real.log ((q.primeFactors.card + 1).factorial : ℝ)) ^ (3 / 4 : ℝ)) :=
    prod_Icc_two_one_add_rpow_le_exp q.primeFactors.card hcard1
  -- Step 4: `(ω(q)+1)! ≤ q`, hence `log (ω(q)+1)! ≤ log q` and we may replace the
  -- base of the exponent.
  have hq1 : 1 ≤ q := by omega
  have hfac : (q.primeFactors.card + 1).factorial ≤ q :=
    Commons.NumberTheory.Nat.factorial_card_primeFactors_le q hq1
  have hfacR : (((q.primeFactors.card + 1).factorial : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hfac
  have hfacpos : (0 : ℝ) < (((q.primeFactors.card + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hlog_le : Real.log (((q.primeFactors.card + 1).factorial : ℕ) : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hfacpos hfacR
  have hlog_nn : 0 ≤ Real.log (((q.primeFactors.card + 1).factorial : ℕ) : ℝ) :=
    Real.log_nonneg (by
      have h : 1 ≤ (q.primeFactors.card + 1).factorial := by
        have := Nat.factorial_pos (q.primeFactors.card + 1); omega
      exact_mod_cast h)
  have hpow_le : (Real.log (((q.primeFactors.card + 1).factorial : ℕ) : ℝ)) ^ (3 / 4 : ℝ)
      ≤ (Real.log (q : ℝ)) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hlog_nn hlog_le (by norm_num)
  have hexp : Real.exp ((Real.log (((q.primeFactors.card + 1).factorial : ℕ) : ℝ)) ^ (3 / 4 : ℝ))
      ≤ Real.exp ((Real.log (q : ℝ)) ^ (3 / 4 : ℝ)) := Real.exp_le_exp.mpr hpow_le
  exact hstep1.trans (hstep2.trans (hstep3.trans hexp))

end Work.LinnikAreas
