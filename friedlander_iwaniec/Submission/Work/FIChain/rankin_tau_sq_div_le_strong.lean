import Mathlib
import Submission.Work.FIChain.TailDefs
import Submission.Work.FIChain.Dpi_rankin
import Submission.Work.FITop.RCPrelude

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIChain

open Finset Filter
open scoped BigOperators

/-- **Rankin's trick, strong form.**

For `κ ≥ 2^30` the tail `Σ_{d ∣ Π(Pz x), d > Δπ} τ(d)²/d` of Rankin's trick is bounded by
`C (log x)^{-65536}`: the general Rankin estimate `Dpi_rankin` (for the exponent `k = 2`) gives
`C (log x)^{-κ/2} (log Pz)^{2^5}`, and the two range facts `(log log x)² ≤ log Pz x ≤ log x`
turn the second factor into `(log x)^{32}`, which the huge saving exponent `κ/2 ≥ 2^29` absorbs. -/
theorem rankin_tau_sq_div_le_strong (κ : ℝ) (hκ : (2 : ℝ) ^ (30 : ℕ) ≤ κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (∑ d ∈ ((Work.FIChain.ProdP (Work.FIChain.Pzc x)).divisors).filter
          (fun d => Work.FIChain.Dpi x κ < d),
          ((d.divisors.card : ℝ)) ^ 2 / (d : ℝ))
        ≤ C * (Real.log (x : ℝ)) ^ (-(65536 : ℤ)) := by
  have hκ1 : (1 : ℝ) ≤ κ := by
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ (30 : ℕ) := by norm_num
    linarith
  obtain ⟨C, hC0, X₀, hC⟩ := Work.FIChain.Dpi_rankin 2 κ hκ1
  have key : ∀ᶠ x : ℕ in Filter.atTop,
      (∑ d ∈ ((Work.FIChain.ProdP (Work.FIChain.Pzc x)).divisors).filter
          (fun d => Work.FIChain.Dpi x κ < d),
          ((d.divisors.card : ℝ)) ^ 2 / (d : ℝ))
        ≤ C * (Real.log (x : ℝ)) ^ (-(65536 : ℤ)) := by
    filter_upwards [eventually_ge_atTop X₀, Work.FITop.FI_ev_log_ge_nat (Real.exp 2),
        Work.FITop.FI_ev_loglog_rpow_le_nat (b := (2:ℝ)) (ε := (1:ℝ)/2) (C := (1:ℝ)/2)
          (by norm_num) (by norm_num)] with x hx0 hLx hLL
    -- the log-log scale is at least 2
    have hM2 : (2:ℝ) ≤ Real.log (Real.log (x:ℝ)) := by
      calc (2:ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
        _ ≤ Real.log (Real.log (x:ℝ)) := Real.log_le_log (Real.exp_pos 2) hLx
    -- `log x ≥ 1`
    have hL1 : (1:ℝ) ≤ Real.log (x:ℝ) := by
      have h3 : (3:ℝ) ≤ Real.log (x:ℝ) := by
        have := Real.add_one_le_exp (2:ℝ); linarith
      linarith
    have hLpos : 0 < Real.log (x:ℝ) := by linarith
    have hlog2le1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have hlog2M2 : Real.log 2 ≤ (Real.log (Real.log (x:ℝ)))^2 := by nlinarith
    have h2log2exp : (2:ℝ) * Real.log 2 ≤ Real.exp 2 := by
      have h2 : (2:ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp (2:ℝ); linarith
      linarith
    -- `Pz x ≥ 2`
    have hPcut2 : (2:ℝ) ≤ ((Work.FITop.Pcut x : ℕ) : ℝ) := by
      have hexp2 : (2:ℝ) ≤ Real.exp ((Real.log (Real.log (x:ℝ)))^2) := by
        have h := Real.exp_le_exp.mpr hlog2M2
        rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h
      exact le_trans hexp2 (Work.FITop.FI_Pcut_ge x)
    have hPz2 : (2:ℕ) ≤ Work.FIChain.Pzc x := by
      show (2:ℕ) ≤ Work.FITop.Pcut x
      exact_mod_cast hPcut2
    -- the two-sided bound `(log log x)² ≤ log Pz x ≤ 2 (log log x)²`
    have hlogPz_ge : (Real.log (Real.log (x:ℝ)))^2 ≤ Real.log ((Work.FIChain.Pzc x : ℕ) : ℝ) :=
      Work.FITop.FI_log_Pcut_ge x
    have hPzle2 : Real.log ((Work.FIChain.Pzc x : ℕ) : ℝ) ≤ 2 * (Real.log (Real.log (x:ℝ)))^2 := by
      have h := Work.FITop.FI_log_Pcut_le x
      have h' : Real.log ((Work.FIChain.Pzc x : ℕ) : ℝ) ≤ Real.log 2 + (Real.log (Real.log (x:ℝ)))^2 := h
      linarith
    have hPnn : 0 ≤ Real.log ((Work.FIChain.Pzc x : ℕ) : ℝ) :=
      le_trans (sq_nonneg (Real.log (Real.log (x:ℝ)))) hlogPz_ge
    have hLhalf : Real.log (x:ℝ) ^ ((1:ℝ)/2) ≤ Real.log (x:ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show ((1:ℝ)/2) ≤ (1:ℝ) by norm_num)
    have hLL2 : (Real.log (Real.log (x:ℝ)))^2 ≤ (1/2) * Real.log (x:ℝ) := by
      rw [Real.rpow_two] at hLL
      have hmul := mul_le_mul_of_nonneg_left hLhalf (by norm_num : (0:ℝ) ≤ 1/2)
      linarith
    have hlog2half : Real.log 2 ≤ (1/2) * Real.log (x:ℝ) := by linarith
    -- `log Pz x ≤ log x`
    have hPleL : Real.log ((Work.FIChain.Pzc x : ℕ) : ℝ) ≤ Real.log (x:ℝ) := by
      have h := Work.FITop.FI_log_Pcut_le x
      have h' : Real.log ((Work.FIChain.Pzc x : ℕ) : ℝ) ≤ Real.log 2 + (Real.log (Real.log (x:ℝ)))^2 := h
      have hA : Real.log 2 + (Real.log (Real.log (x:ℝ)))^2 ≤
          (1/2)*Real.log (x:ℝ) + (1/2)*Real.log (x:ℝ) := add_le_add hlog2half hLL2
      have hB : (1/2)*Real.log (x:ℝ) + (1/2)*Real.log (x:ℝ) = Real.log (x:ℝ) := by ring
      rw [hB] at hA
      exact le_trans h' hA
    -- Rankin's estimate for `k = 2`
    have hb := hC x (Work.FIChain.Pzc x) hx0 hPz2 hM2 hlogPz_ge hPzle2
    have hPpow_le : (Real.log ((Work.FIChain.Pzc x : ℕ) : ℝ)) ^ (2^(2+3:ℕ)) ≤
        (Real.log (x:ℝ)) ^ (2^(2+3:ℕ)) := pow_le_pow_left₀ hPnn hPleL _
    have hDnn : 0 ≤ C * (Real.log (x:ℝ)) ^ (-(κ/2)) :=
      mul_nonneg hC0.le (Real.rpow_nonneg hLpos.le _)
    have hLpow_mul : (Real.log (x:ℝ)) ^ (-(κ/2)) * (Real.log (x:ℝ)) ^ (2^(2+3:ℕ))
        = (Real.log (x:ℝ)) ^ (-(κ/2) + (((2^(2+3:ℕ) : ℕ)) : ℝ)) := by
      have h := Real.rpow_add hLpos (-(κ/2)) (((2^(2+3:ℕ) : ℕ)) : ℝ)
      rw [Real.rpow_natCast] at h
      exact h.symm
    have hpowle32 : (((2^(2+3:ℕ) : ℕ)) : ℝ) ≤ 32 := by
      have : (2:ℕ)^(2+3) = 32 := by norm_num
      rw [this]; norm_num
    have hk : (131136:ℝ) ≤ κ := by norm_num at hκ; linarith
    have hexp : -(κ/2) + (((2^(2+3:ℕ) : ℕ)) : ℝ) ≤ -65536 := by
      have : (32:ℝ) - κ/2 ≤ -65536 := by linarith
      linarith
    have hz : (Real.log (x:ℝ)) ^ (-65536 : ℝ) = (Real.log (x:ℝ)) ^ (-(65536:ℤ)) := by
      rw [← Real.rpow_intCast (Real.log (x:ℝ)) (-(65536:ℤ))]
      norm_num
    calc
      (∑ d ∈ ((Work.FIChain.ProdP (Work.FIChain.Pzc x)).divisors).filter
          (fun d => Work.FIChain.Dpi x κ < d),
          ((d.divisors.card : ℝ)) ^ 2 / (d : ℝ))
          ≤ C * (Real.log (x:ℝ)) ^ (-(κ/2)) *
              (Real.log ((Work.FIChain.Pzc x : ℕ) : ℝ)) ^ (2^(2+3:ℕ)) := hb
      _ ≤ C * (Real.log (x:ℝ)) ^ (-(κ/2)) * (Real.log (x:ℝ)) ^ (2^(2+3:ℕ)) :=
            mul_le_mul_of_nonneg_left hPpow_le hDnn
      _ = C * ((Real.log (x:ℝ)) ^ (-(κ/2)) * (Real.log (x:ℝ)) ^ (2^(2+3:ℕ))) := by ring
      _ = C * (Real.log (x:ℝ)) ^ (-(κ/2) + (((2^(2+3:ℕ) : ℕ)) : ℝ)) := by rw [hLpow_mul]
      _ ≤ C * (Real.log (x:ℝ)) ^ (-65536 : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 hexp) hC0.le
      _ = C * (Real.log (x:ℝ)) ^ (-(65536:ℤ)) := by rw [hz]
  refine ⟨C, hC0, ?_⟩
  exact Filter.eventually_atTop.mp key

end Work.FIChain
