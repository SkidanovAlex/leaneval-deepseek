import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Commons.NumberTheory.Mertens.tsum_primes_eq_sum_rpowDiff
import Submission.Commons.Analysis.ExpLog.log_le_rpow_div
import Submission.Commons.NumberTheory.Mertens.summable_weighted_error

open Filter Finset
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

/-! # Summability of `∑ log log k · (k^{-ε} − (k+1)^{-ε})`

For every `0 < ε`, the weighted difference series converges.  We prove it by
comparing (for `3 ≤ k`) the summand with `2 * k^(-1-ε/2)`, a convergent
`p`-series.  Three elementary facts are needed on `[3,∞)`:

* `1 < log k`, hence `0 ≤ log log k ≤ log k`;
* `log k ≤ (2/ε) · k^{ε/2}` (sub-polynomial growth of `log`, via
  `Commons.Analysis.ExpLog.log_le_rpow_div`);
* `k^{-ε} − (k+1)^{-ε} ≤ ε · k^{-ε-1}` (a Bernoulli-type estimate).
-/

private lemma log_k_gt_one {k : ℕ} (hk : 3 ≤ k) : (1 : ℝ) < Real.log (k : ℝ) := by
  have hek : Real.exp 1 < (k : ℝ) := lt_of_lt_of_le Real.exp_one_lt_three (by exact_mod_cast hk)
  have hle : Real.log (Real.exp 1) < Real.log (k : ℝ) :=
    Real.log_lt_log (Real.exp_pos 1) hek
  simpa using hle

private lemma loglog_k_nonneg {k : ℕ} (hk : 3 ≤ k) : 0 ≤ Real.log (Real.log (k : ℝ)) := by
  have h1 : (1 : ℝ) ≤ Real.log (k : ℝ) := le_of_lt (log_k_gt_one hk)
  have := Real.log_le_log (by norm_num : (0 : ℝ) < 1) h1
  simpa using this

private lemma loglog_k_le_log_k {k : ℕ} (hk : 3 ≤ k) :
    Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ) := by
  have hlogk_pos : 0 < Real.log (k : ℝ) := lt_trans zero_lt_one (log_k_gt_one hk)
  have h := Real.log_le_sub_one_of_pos hlogk_pos
  linarith

/-- Bernoulli-type estimate: `1 − (1+u)^{-ε} ≤ ε·u` for `ε > 0`, `u ≥ 0`. -/
private lemma one_sub_rpow_neg_le {ε u : ℝ} (hε : 0 < ε) (hu : 0 ≤ u) :
    1 - (1 + u) ^ (-ε) ≤ ε * u := by
  have hu1 : 0 < 1 + u := by linarith
  have hlog : Real.log (1 + u) ≤ u := by
    have hL := Real.log_le_sub_one_of_pos hu1
    linarith
  have hEmul : ε * Real.log (1 + u) ≤ ε * u :=
    mul_le_mul_of_nonneg_left hlog (le_of_lt hε)
  have harg : -ε * u ≤ -ε * Real.log (1 + u) := by
    have h1 : -(ε * u) ≤ -(ε * Real.log (1 + u)) := neg_le_neg hEmul
    simpa [neg_mul] using h1
  have hExp_ge : Real.exp (-ε * u) ≤ Real.exp (-ε * Real.log (1 + u)) :=
    Real.exp_le_exp.mpr harg
  have hB : 1 - ε * u ≤ Real.exp (-ε * u) := by
    have hA := Real.add_one_le_exp (-ε * u)
    linarith
  calc
    1 - (1 + u) ^ (-ε) = 1 - Real.exp (Real.log (1 + u) * (-ε)) := by
      rw [Real.rpow_def_of_pos hu1]
    _ ≤ 1 - Real.exp (-ε * u) := by
      --  exp (log (1+u)*(-ε)) = exp ((-ε)*log(1+u)) ≥ exp(-ε*u)
      have hEq : Real.exp (Real.log (1 + u) * (-ε)) = Real.exp (-ε * Real.log (1 + u)) := by
        congr 1
        ring
      rw [hEq]
      have hle2 : Real.exp (-ε * Real.log (1 + u)) ≥ Real.exp (-ε * u) := hExp_ge
      linarith
    _ ≤ ε * u := by linarith

/-- `k^{-ε} − (k+1)^{-ε} ≤ ε·k^{-ε-1}` for `1 ≤ k`, `0 < ε`. -/
private lemma rpowDiff_le_mul_rpow {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε)) ≤ ε * (k : ℝ) ^ (-ε - 1) := by
  have hK : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hK0 : 0 ≤ (k : ℝ) := le_of_lt hK
  have hKne : (k : ℝ) ≠ 0 := ne_of_gt hK
  have hk1pos : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hmul : (((k + 1 : ℕ) : ℝ) = (k : ℝ) * (1 + (1 : ℝ) / (k : ℝ))) := by
    calc
      ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
      _ = (k : ℝ) * (1 + (1 : ℝ) / (k : ℝ)) := by field_simp [hKne]
  have hratio_pos : 0 < (1 + (1 : ℝ) / (k : ℝ)) := by positivity
  have hratio_nonneg : 0 ≤ (1 + (1 : ℝ) / (k : ℝ)) := le_of_lt hratio_pos
  have hber : 1 - (1 + (1 : ℝ) / (k : ℝ)) ^ (-ε) ≤ ε * ((1 : ℝ) / (k : ℝ)) :=
    one_sub_rpow_neg_le hε (by positivity)
  have hfact : ((((k + 1 : ℕ) : ℝ) ^ (-ε))) =
      (k : ℝ) ^ (-ε) * (1 + (1 : ℝ) / (k : ℝ)) ^ (-ε) := by
    calc
      (((k + 1 : ℕ) : ℝ) ^ (-ε)) = ((k : ℝ) * (1 + (1 : ℝ) / (k : ℝ))) ^ (-ε) := by rw [hmul]
      _ = (k : ℝ) ^ (-ε) * (1 + (1 : ℝ) / (k : ℝ)) ^ (-ε) :=
        Real.mul_rpow hK0 hratio_nonneg
  calc
    ((k : ℝ) ^ (-ε)) - ((((k + 1 : ℕ) : ℝ) ^ (-ε)))
        = (k : ℝ) ^ (-ε) * (1 - (1 + (1 : ℝ) / (k : ℝ)) ^ (-ε)) := by
            rw [hfact]
            ring
    _ ≤ (k : ℝ) ^ (-ε) * (ε * ((1 : ℝ) / (k : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hber (Real.rpow_nonneg hK0 (-ε))
    _ = ε * (k : ℝ) ^ (-ε - 1) := by
            have hrpow : (k : ℝ) ^ (-ε - 1) = (k : ℝ) ^ (-ε) * (k : ℝ) ^ (-1 : ℝ) := by
              rw [show (-ε - 1) = (-ε) + (-1 : ℝ) by ring]
              exact Real.rpow_add hK (-ε) (-1 : ℝ)
            calc
              (k : ℝ) ^ (-ε) * (ε * ((1 : ℝ) / (k : ℝ)))
                  = ε * ((k : ℝ) ^ (-ε) * (k : ℝ) ^ (-1 : ℝ)) := by
                      rw [Real.rpow_neg_one]
                      field_simp [hKne]
              _ = ε * (k : ℝ) ^ (-ε - 1) := by rw [hrpow]

/-- `log k ≤ (2/ε)·k^{ε/2}` for `3 ≤ k`, `0 < ε`. -/
private lemma log_k_le_rpow {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 3 ≤ k) :
    Real.log (k : ℝ) ≤ (2 / ε) * (k : ℝ) ^ (ε / 2) := by
  have hw : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have ha : 0 < ε / 2 := by positivity
  have h1 := Commons.Analysis.ExpLog.log_le_rpow_div (w := (k : ℝ)) (a := ε / 2) hw ha
  calc
    Real.log (k : ℝ) ≤ (k : ℝ) ^ (ε / 2) / (ε / 2) := h1
    _ = (2 / ε) * (k : ℝ) ^ (ε / 2) := by
      field_simp [hε.ne']

/-- Summability of the weighted `log log`-difference series. -/
theorem summable_weighted_loglog {ε : ℝ} (hε : 0 < ε) :
    Summable (fun k : ℕ => if 2 ≤ k then
      Real.log (Real.log (k : ℝ)) *
        (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0) := by
  let f : ℕ → ℝ := fun k => if 2 ≤ k then
      Real.log (Real.log (k : ℝ)) *
        (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0
  let g : ℕ → ℝ := fun k => 2 * (k : ℝ) ^ (-1 - ε / 2)
  have hg_summ : Summable g := by
    have hps : Summable (fun k : ℕ => (k : ℝ) ^ (-1 - ε / 2)) := by
      exact (Real.summable_nat_rpow).2 (by linarith)
    simpa [g] using hps.mul_left 2
  have hb : ∀ᶠ k in atTop, ‖f k‖ ≤ g k := by
    filter_upwards [eventually_ge_atTop 3] with k hk3
    have hk2 : 2 ≤ k := by omega
    have hk1 : 1 ≤ k := by omega
    have hf_nonneg : 0 ≤ f k := by
      dsimp [f]
      rw [if_pos hk2]
      exact mul_nonneg (loglog_k_nonneg hk3) (rpowDiff_nonneg hε hk1)
    have hf_le : f k ≤ g k := by
      dsimp [f, g]
      rw [if_pos hk2]
      have hd : 0 ≤ ((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε)) :=
        rpowDiff_nonneg hε hk1
      have hl : 0 ≤ Real.log (k : ℝ) := le_of_lt (lt_trans zero_lt_one (log_k_gt_one hk3))
      have hc : 0 ≤ ε * (k : ℝ) ^ (-ε - 1) := by
        exact mul_nonneg (le_of_lt hε) (Real.rpow_nonneg (by exact_mod_cast (by omega : 0 ≤ k)) (-ε - 1))
      calc
        Real.log (Real.log (k : ℝ)) *
              (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε)))
            ≤ Real.log (k : ℝ) *
              (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) := by
                exact mul_le_mul_of_nonneg_right (loglog_k_le_log_k hk3) hd
        _ ≤ Real.log (k : ℝ) * (ε * (k : ℝ) ^ (-ε - 1)) := by
                exact mul_le_mul_of_nonneg_left (rpowDiff_le_mul_rpow hε hk1) hl
        _ ≤ ((2 / ε) * (k : ℝ) ^ (ε / 2)) * (ε * (k : ℝ) ^ (-ε - 1)) := by
                exact mul_le_mul_of_nonneg_right (log_k_le_rpow hε hk3) hc
        _ ≤ 2 * (k : ℝ) ^ (-1 - ε / 2) := by
                have hK : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
                have hEq : ((2 / ε) * (k : ℝ) ^ (ε / 2)) * (ε * (k : ℝ) ^ (-ε - 1))
                      = 2 * (k : ℝ) ^ (-1 - ε / 2) := by
                  calc
                    ((2 / ε) * (k : ℝ) ^ (ε / 2)) * (ε * (k : ℝ) ^ (-ε - 1))
                        = 2 * ((k : ℝ) ^ (ε / 2) * (k : ℝ) ^ (-ε - 1)) := by
                            field_simp [hε.ne']
                    _ = 2 * (k : ℝ) ^ (ε / 2 + (-ε - 1)) := by
                            rw [← Real.rpow_add hK (ε / 2) (-ε - 1)]
                    _ = 2 * (k : ℝ) ^ (-1 - ε / 2) := by
                            rw [show ε / 2 + (-ε - 1) = -1 - ε / 2 by ring]
                rw [hEq]
    calc
      ‖f k‖ = f k := by simp [Real.norm_eq_abs, abs_of_nonneg hf_nonneg]
      _ ≤ g k := hf_le
  change Summable f
  exact Summable.of_norm_bounded_eventually_nat (f := f) (g := g) hg_summ hb

end Commons.NumberTheory.Mertens