import Mathlib
import Submission.Work.RHContract.A.regionII.caC1_cert_defs

/-!
# The arithmetic tail bound underlying the `Margin.caC1` certificate in region II

For a cutoff `j = p - 1 ≥ 500` and the tail value `t` attached to it by the certificate, the
integer check `688·10^46 ≤ t·j·(2⌊10^9 log j⌋ − A)` forces the analytic tail bound

`(43/100)·1/(√ξ log ξ) ≤ t/10^40`

whenever `ξ ≥ j²/2.5`.  The passage is purely arithmetic:

* `A = utOf 5 - ltOf 2 ≥ 10^9 log 2.5`, so `2·ltOf j - A ≤ 10^9 log ξ` (using `ξ ≥ j²/2.5`);
* hence `t ≥ 688·10^46/(j·10^9·log ξ)`, i.e. `t/10^40 ≥ (688/1000)/(j log ξ)`;
* `√ξ ≥ j/√2.5` and `√2.5 ≤ 8/5`, so `(43/100)·j ≤ (688/1000)·√ξ`;
* dividing by `log ξ > 0` gives the claim.
-/

namespace Work.RHContract.A.regionII

open Commons.NumberTheory.Chebyshev
open Commons.NumberTheory.Chebyshev.ThetaBracket

/-- The certified upper bracket `utOf 5` of `10^9 log 5`. -/
lemma caC1_tail_utOf_five : (utOf 5 : ℕ) = 1611320000 := by decide

/-- `A = utOf 5 - ltOf 2` dominates `10^9 log 2.5 = 10^9 (log 5 - log 2)`. -/
lemma caC1_tail_certA_ge_log25 : 10^9 * Real.log (2.5:ℝ) ≤ (certA : ℝ) := by
  have h5 : 10^9 * Real.log 5 ≤ (utOf 5 : ℝ) := log_le_utOf 5 (by norm_num)
  have h2 : (693147000 : ℝ) ≤ 10^9 * Real.log 2 := log2_ge
  have hlog25 : Real.log (2.5:ℝ) = Real.log 5 - Real.log 2 := by
    rw [show (2.5:ℝ) = 5/2 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  have hcert : (certA : ℝ) = 918173000 := by
    rw [certA_eq]; norm_num
  rw [hlog25, mul_sub, hcert]
  have h5v : (utOf 5 : ℝ) = 1611320000 := by rw [caC1_tail_utOf_five]; norm_num
  linarith

/-- `√2.5 ≤ 8/5`. -/
lemma caC1_tail_sqrt25_le : Real.sqrt (2.5:ℝ) ≤ 8/5 := by
  rw [Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 8/5)]
  norm_num

/-- The numerical consumption of `√2.5 ≤ 8/5`: `43/100 ≤ (688/1000)/√2.5`. -/
lemma caC1_tail_const_ineq : (43/100 : ℝ) ≤ (688/1000) / Real.sqrt 2.5 := by
  have hsqrt25pos : 0 < Real.sqrt (2.5:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have ha : (43/100) * Real.sqrt (2.5:ℝ) ≤ 688/1000 := by nlinarith [caC1_tail_sqrt25_le]
  rw [le_div_iff₀ hsqrt25pos]
  linarith [ha]

theorem caC1_tail_arith {p t : ℕ} {ξ : ℝ} (hp : 501 ≤ p)
    (hξ : ((p : ℝ) - 1) ^ 2 / 2.5 ≤ ξ)
    (ht : 688 * 10 ^ 46 ≤ t * (p - 1) * (2 * Commons.NumberTheory.Chebyshev.ThetaBracket.ltOf (p - 1) - Work.RHContract.A.regionII.certA)) :
    (43 / 100) * (1 / (Real.sqrt ξ * Real.log ξ)) ≤ (t : ℝ) / 10 ^ 40 := by
  -- Abstract the (definitionally expensive) constant `certA = utOf 5 - ltOf 2` away, so that
  -- context-scanning tactics do not attempt to unfold it.
  generalize hAcert : certA = A at ht
  set j : ℕ := p - 1 with hj
  have hj500 : 500 ≤ j := by omega
  have hj2 : 2 ≤ j := by omega
  have hjpos : 0 < j := by omega
  have hjR : (0:ℝ) < (j:ℝ) := by exact_mod_cast hjpos
  have hcastj : (j:ℝ) = (p:ℝ) - 1 := by
    rw [hj, Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
  have hξ' : (j:ℝ)^2/2.5 ≤ ξ := by rw [← hcastj] at hξ; exact hξ
  have hξ_big : (1:ℝ) < ξ := by
    have hjR' : (500:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj500
    have hsq : (500:ℝ)^2 ≤ (j:ℝ)^2 := by nlinarith
    have hdiv : (500:ℝ)^2/2.5 ≤ (j:ℝ)^2/2.5 := div_le_div_of_nonneg_right hsq (by norm_num)
    have h500 : (500:ℝ)^2/2.5 = 100000 := by norm_num
    have h100 : (100000:ℝ) ≤ (j:ℝ)^2/2.5 := by linarith [hdiv, h500]
    linarith [hξ', h100]
  have hlogξ : 0 < Real.log ξ := Real.log_pos hξ_big
  have hsqrtξ : 0 < Real.sqrt ξ := Real.sqrt_pos.mpr (by linarith)
  have hcertA : 10^9 * Real.log (2.5:ℝ) ≤ (A:ℝ) := by
    have h := caC1_tail_certA_ge_log25
    rw [hAcert] at h
    exact h
  have hA_le : ((2 * ltOf j - A : ℕ) : ℝ) ≤ 10^9 * Real.log ξ := by
    have hlogj : (ltOf j : ℝ) ≤ 10^9 * Real.log j := ltOf_le_log j hj2
    by_cases hc : A ≤ 2 * ltOf j
    · have hcast : ((2 * ltOf j - A : ℕ) : ℝ) = 2*(ltOf j:ℝ) - (A:ℝ) := by
        rw [Nat.cast_sub hc, Nat.cast_mul]; norm_num
      rw [hcast]
      have heq : Real.log ((j:ℝ)^2/2.5) = 2*Real.log j - Real.log 2.5 := by
        rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]
        push_cast; ring
      have hmid : 2*(ltOf j:ℝ) - (A:ℝ) ≤ 10^9 * Real.log ((j:ℝ)^2/2.5) := by
        rw [heq]; nlinarith [hlogj, hcertA]
      calc 2*(ltOf j:ℝ) - (A:ℝ) ≤ 10^9 * Real.log ((j:ℝ)^2/2.5) := hmid
        _ ≤ 10^9 * Real.log ξ := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact Real.log_le_log (by positivity) hξ'
    · have h0 : (2*ltOf j - A : ℕ) = 0 :=
        Nat.sub_eq_zero_of_le (le_of_lt (lt_of_not_ge hc))
      rw [h0]; push_cast
      exact mul_nonneg (by norm_num) (le_of_lt hlogξ)
  have htR : (688 * 10^46 : ℝ) ≤ (t:ℝ) * (j:ℝ) * ((2*ltOf j - A : ℕ):ℝ) := by
    exact_mod_cast ht
  have hkey : (688 * 10^46 : ℝ) ≤ (t:ℝ) * ((j:ℝ) * (10^9 * Real.log ξ)) := by
    have h1 : (688 * 10^46 : ℝ) ≤ (t:ℝ) * (j:ℝ) * (10^9 * Real.log ξ) := by
      refine le_trans htR ?_
      exact mul_le_mul_of_nonneg_left hA_le (by positivity)
    rwa [mul_assoc] at h1
  have hDpos : 0 < (j:ℝ) * (10^9 * Real.log ξ) := by positivity
  have ht_lb : (688 * 10^46 : ℝ) / ((j:ℝ) * (10^9 * Real.log ξ)) ≤ (t:ℝ) := by
    rw [div_le_iff₀ hDpos]; exact hkey
  have hstep1 : ((688 * 10^46 : ℝ) / ((j:ℝ) * (10^9 * Real.log ξ))) / 10^40 ≤ (t:ℝ) / 10^40 :=
    div_le_div_of_nonneg_right ht_lb (by norm_num)
  have hsimp : ((688 * 10^46 : ℝ) / ((j:ℝ) * (10^9 * Real.log ξ))) / 10^40
      = (688/1000) / ((j:ℝ) * Real.log ξ) := by
    have hjne : (j:ℝ) ≠ 0 := ne_of_gt hjR
    have hLne : Real.log ξ ≠ 0 := ne_of_gt hlogξ
    field_simp; norm_num
  have hcc : (43/100) * (j:ℝ) ≤ (688/1000) * Real.sqrt ξ := by
    have hsqrtξ_ge : (j:ℝ)/Real.sqrt 2.5 ≤ Real.sqrt ξ := by
      have h1 : Real.sqrt ((j:ℝ)^2/2.5) ≤ Real.sqrt ξ := Real.sqrt_le_sqrt hξ'
      rw [Real.sqrt_div (sq_nonneg (j:ℝ)) 2.5, Real.sqrt_sq (le_of_lt hjR)] at h1
      exact h1
    have h1 : (688/1000) * ((j:ℝ)/Real.sqrt 2.5) ≤ (688/1000) * Real.sqrt ξ :=
      mul_le_mul_of_nonneg_left hsqrtξ_ge (by norm_num)
    have h2 : (43/100) * (j:ℝ) ≤ (688/1000) * ((j:ℝ)/Real.sqrt 2.5) := by
      have hm := mul_le_mul_of_nonneg_right caC1_tail_const_ineq (le_of_lt hjR)
      calc (43/100) * (j:ℝ) ≤ ((688/1000)/Real.sqrt 2.5) * (j:ℝ) := hm
        _ = (688/1000) * ((j:ℝ)/Real.sqrt 2.5) := by ring
    linarith
  have hAux : (43/100)/Real.sqrt ξ ≤ (688/1000)/(j:ℝ) := by
    rw [div_le_iff₀ hsqrtξ, div_mul_eq_mul_div]
    rw [le_div_iff₀ hjR]
    exact hcc
  have hstep2 : (43/100) * (1 / (Real.sqrt ξ * Real.log ξ)) ≤ (688/1000) / ((j:ℝ) * Real.log ξ) := by
    calc (43/100) * (1 / (Real.sqrt ξ * Real.log ξ))
        = ((43/100)/Real.sqrt ξ) * (1/Real.log ξ) := by field_simp
      _ ≤ ((688/1000)/(j:ℝ)) * (1/Real.log ξ) :=
          mul_le_mul_of_nonneg_right hAux (le_of_lt (one_div_pos.mpr hlogξ))
      _ = (688/1000) / ((j:ℝ) * Real.log ξ) := by field_simp
  calc (43/100) * (1 / (Real.sqrt ξ * Real.log ξ))
      ≤ (688/1000) / ((j:ℝ) * Real.log ξ) := hstep2
    _ = ((688 * 10^46 : ℝ) / ((j:ℝ) * (10^9 * Real.log ξ))) / 10^40 := hsimp.symm
    _ ≤ (t:ℝ)/10^40 := hstep1

end Work.RHContract.A.regionII
