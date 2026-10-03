import Mathlib
import Submission.Work.FITop3.Defs3

/-!
# `Work.FIArea6.crude_arith` — the elementary arithmetic of the crude pointwise route

`T = 2^{log(2N)/log P}` is the `NoSmallPrimes` cap on `τ(|z|²)`.  The crude pointwise estimate
of `beta_sq_mass_tight` (`crude_case`) needs the two pointwise bounds

* `Pa.θ · T² ≤ 1.67 · (log(2+N))³`, and
* `T² ≤ 1.67 · √N · (log(2+N))³`,

proved here from the two genuinely numerical hypotheses on the set-up:
`log log x > 20` (so `N` is enormous, `log N > 10^8`) and the exponent relation
`(10.12)+` relating `A'` to `log N` — the latter is what makes `θ = (log x)^{-A'}` small enough
to beat the `τ`-cap even in the (only non-elementary) regime `log log x > 20`.

The proof is pure `exp`/`log` bookkeeping.  Writing `n = log N`, `u = log log x`, `p = log P`:

* `u > 20 ⟹ p ≥ u² > 400`, so `2 log 2 · log(2N)/p ≤ 0.0035 (1+n)` and hence
  `T² ≤ exp(0.0035(1+n))`;
* `exp(0.0035(1+n)) ≤ √N = exp(n/2)` because `n > 10^8`;
* `θ = exp(-A' u) < exp(-n/3 + 4000(1 + log n))`, so
  `θ T² ≤ exp(-0.32 n + 4000.0035 + 4000 log n) ≤ exp(3 log n) ≤ 1.67 (log(2+N))³`,
  the middle inequality being `3997 log n + 4000.0035 ≤ 0.32 n`, which follows from
  `log n ≤ 4 n^{1/4}` (`Real.log_le_rpow_div`) together with `n ≥ 10^8 ⟹ n^{1/4} ≥ 100`.
-/

set_option autoImplicit false

namespace Work.FIArea6

noncomputable section

/-- `Real.log 2 ≤ 0.7`. -/
private lemma log_two_le : Real.log 2 ≤ 0.7 :=
  le_trans Real.log_two_lt_d9.le (by norm_num)

/-- **The final numerical inequality.**  For `n ≥ 10^8`, `3997 log n + 4000.0035 ≤ 0.32 n`.

With `t = n^{1/4}` and `log n ≤ 4 n^{1/4} = 4t` (`Real.log_le_rpow_div`, `ε = 1/4`) this is
`15988 t + 4000.0035 ≤ 0.32 t⁴`, which holds because `t ≥ 100` gives `t⁴ ≥ 10^6 t` and hence
`0.32 t⁴ ≥ 320000 t ≥ 15988 t + 4000.0035`. -/
private lemma key_log_bound (n : ℝ) (hn : (1e8:ℝ) ≤ n) :
    3997 * Real.log n + 4000.0035 ≤ 0.32 * n := by
  have hn_pos : 0 < n := by linarith
  set t : ℝ := n ^ ((1:ℝ)/4) with ht
  have ht100 : (100:ℝ) ≤ t := by
    rw [ht]
    have h1004 : (100:ℝ)^4 = 1e8 := by norm_num
    have h2 : (100:ℝ)^4 ≤ n := by rw [h1004]; exact hn
    have h3 : ((100:ℝ)^4)^((1:ℝ)/4) ≤ n ^ ((1:ℝ)/4) :=
      Real.rpow_le_rpow (by positivity) h2 (by norm_num)
    have h4 : ((100:ℝ)^4)^((1:ℝ)/4) = 100 := by
      rw [show ((100:ℝ)^4) = ((100:ℝ)^((4:ℕ):ℝ)) by rw [Real.rpow_natCast]]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 100)]
      norm_num
    linarith [h3, h4.le]
  have ht4 : t^4 = n := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]
    norm_num
  have ht_pos : 0 < t := by linarith
  have hlog_le : Real.log n ≤ 4 * t := by
    have h := Real.log_le_rpow_div hn_pos.le (by norm_num : (0:ℝ) < (1:ℝ)/4)
    have h2 : n ^ ((1:ℝ)/4) / ((1:ℝ)/4) = 4 * t := by
      rw [ht, div_eq_mul_inv]; norm_num; ring
    linarith [h, h2.le]
  have ht3 : (100:ℝ)^3 ≤ t^3 := pow_le_pow_left₀ (by norm_num) ht100 3
  have h1 : (100:ℝ)^3 * t ≤ t^4 := by nlinarith [ht3, ht_pos]
  have h2 : 0.32 * ((100:ℝ)^3 * t) ≤ 0.32 * n := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [← ht4]; exact h1
  have h3 : (0.32:ℝ) * ((100:ℝ)^3 * t) = 320000 * t := by norm_num; ring
  have h4 : 3997 * Real.log n ≤ 3997 * (4*t) :=
    mul_le_mul_of_nonneg_left hlog_le (by norm_num)
  have h5 : (3997:ℝ) * (4*t) = 15988 * t := by ring
  have h6 : 15988 * t + 4000.0035 ≤ 320000 * t := by nlinarith [ht100]
  linarith [h4, h5, h6, h2, h3]

/-- **The elementary arithmetic of the crude pointwise route.** -/
theorem crude_arith (Pa : Work.FITop.Params)
    (hu20 : 20 < Real.log (Real.log (Pa.x : ℝ)))
    (hlogN : (1e8:ℝ) < Real.log (Pa.N : ℝ)) (hN1 : (1:ℝ) ≤ Pa.N)
    (hAb : Real.log (Pa.N) / 3 - 4000 * (1 + Real.log (Real.log (Pa.N : ℝ)))
      < Pa.A' * Real.log (Real.log (Pa.x : ℝ))) :
    Pa.θ * ((2:ℝ) ^ (Real.log (2 * Pa.N) / Real.log (Pa.Pz : ℝ)))^2
        ≤ 1.67 * (Real.log (2 + Pa.N))^3
      ∧ ((2:ℝ) ^ (Real.log (2 * Pa.N) / Real.log (Pa.Pz : ℝ)))^2
        ≤ 1.67 * Real.sqrt Pa.N * (Real.log (2 + Pa.N))^3 := by
  set u : ℝ := Real.log (Real.log (Pa.x : ℝ)) with hu
  set n : ℝ := Real.log (Pa.N : ℝ) with hn
  set p : ℝ := Real.log (Pa.Pz : ℝ) with hp
  -- basic facts
  have hx1 : (1:ℝ) < (Pa.x : ℝ) := by
    have hx3 : (3:ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hlogx1 : 0 < Real.log (Pa.x : ℝ) := Real.log_pos hx1
  have hu20' : 20 < u := hu20
  have hn_gt : (1e8:ℝ) < n := hlogN
  have hn_pos : 0 < n := by linarith
  have hNpos : 0 < (Pa.N : ℝ) := by linarith
  have hp_ge : u^2 ≤ p := by
    have h := Pa.hPlo
    rw [← hu, ← hp] at h
    exact h
  have hp_gt : (400:ℝ) < p := by nlinarith [hu20', hp_ge, sq_nonneg u]
  have hp_pos : 0 < p := by linarith
  have hlog2N_eq : Real.log (2 * Pa.N) = Real.log 2 + n := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hNpos.ne', hn]
  have hlog2N_le : Real.log (2 * Pa.N) ≤ 1 + n := by
    rw [hlog2N_eq]; linarith [log_two_le]
  have hlog2N_pos : 0 < Real.log (2 * Pa.N) := by
    rw [hlog2N_eq]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hlogN2_ge : n ≤ Real.log (2 + Pa.N) := by
    rw [hn]
    apply Real.log_le_log hNpos
    linarith
  have hlogN2_ge_one : (1:ℝ) ≤ Real.log (2 + Pa.N) := by
    have h3 : (3:ℝ) ≤ 2 + Pa.N := by linarith
    have hle := Real.log_le_log (by norm_num : (0:ℝ) < 3) h3
    have hlog3 : 1 < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h
    linarith
  have hcube_one : (1:ℝ) ≤ (Real.log (2 + Pa.N))^3 := one_le_pow₀ hlogN2_ge_one
  -- the numerical inequality
  have hkey : 3997 * Real.log n + 4000.0035 ≤ 0.32 * n := key_log_bound n hn_gt.le
  -- `T²` bound
  have hT_eq : ((2:ℝ) ^ (Real.log (2 * Pa.N) / p))^2
      = Real.exp (2 * (Real.log 2 * (Real.log (2 * Pa.N) / p))) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), ← Real.exp_nat_mul]
    ring_nf
  have hT_le : ((2:ℝ) ^ (Real.log (2 * Pa.N) / p))^2 ≤ Real.exp (0.0035 * (1 + n)) := by
    rw [hT_eq]
    apply Real.exp_le_exp.mpr
    have hLpos : 0 ≤ Real.log (2 * Pa.N) / p := div_nonneg hlog2N_pos.le hp_pos.le
    have h1 : Real.log (2 * Pa.N) / p ≤ (1 + n) / p :=
      div_le_div_of_nonneg_right hlog2N_le hp_pos.le
    have h2 : (1 + n) / p ≤ (1 + n) / 400 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num : (0:ℝ) < 400) hp_gt.le
    have h3 : Real.log 2 * (Real.log (2 * Pa.N) / p) ≤ 0.7 * ((1 + n)/400) :=
      mul_le_mul log_two_le (le_trans h1 h2) hLpos (by norm_num)
    calc 2 * (Real.log 2 * (Real.log (2 * Pa.N) / p)) ≤ 2 * (0.7 * ((1 + n)/400)) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = 0.0035 * (1 + n) := by ring
  have hsqrt : Real.sqrt Pa.N = Real.exp (n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNpos, ← hn]; ring_nf
  -- the exponent inequality
  have hE_le : (-(n/3) + 4000 * (1 + Real.log n)) + 0.0035 * (1 + n)
      ≤ 3 * Real.log n + Real.log 1.67 := by
    have hlog167 : 0 ≤ Real.log 1.67 := Real.log_nonneg (by norm_num)
    have hcoef : n * (0.0035 - 1/3) ≤ -0.32 * n := by
      have hc : (0.0035:ℝ) - 1/3 ≤ -0.32 := by norm_num
      have := mul_le_mul_of_nonneg_left hc hn_pos.le
      linarith [this]
    have hkey' : -0.32 * n + 4000.0035 + 4000 * Real.log n ≤ 3 * Real.log n := by
      linarith [hkey]
    have hid : (-(n/3) + 4000 * (1 + Real.log n)) + 0.0035 * (1 + n)
        = n * (0.0035 - 1/3) + 4000.0035 + 4000 * Real.log n := by ring
    rw [hid]
    linarith [hcoef, hkey', hlog167]
  refine ⟨?_, ?_⟩
  · -- first conjunct
    have htheta : Pa.θ = Real.exp (-(Pa.A' * u)) := by
      rw [Pa.hθ, Real.rpow_def_of_pos hlogx1]
      congr 1
      rw [← hu]
      ring
    have htheta_le : Pa.θ ≤ Real.exp (-(n/3) + 4000 * (1 + Real.log n)) := by
      rw [htheta]
      apply Real.exp_le_exp.mpr
      linarith [hAb]
    calc Pa.θ * ((2:ℝ) ^ (Real.log (2 * Pa.N) / p))^2
        ≤ Real.exp (-(n/3) + 4000 * (1 + Real.log n)) * Real.exp (0.0035 * (1 + n)) := by
          apply mul_le_mul htheta_le hT_le (sq_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((-(n/3) + 4000 * (1 + Real.log n)) + 0.0035 * (1 + n)) :=
          (Real.exp_add _ _).symm
      _ ≤ Real.exp (3 * Real.log n + Real.log 1.67) := Real.exp_le_exp.mpr hE_le
      _ = 1.67 * n^3 := by
          have h3log : Real.exp (3 * Real.log n) = n ^ 3 := by
            have h33 : (3:ℝ) * Real.log n = ((3:ℕ):ℝ) * Real.log n := by norm_num
            rw [h33, Real.exp_nat_mul, Real.exp_log hn_pos]
          rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 1.67), h3log]
          ring
      _ ≤ 1.67 * (Real.log (2 + Pa.N))^3 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact pow_le_pow_left₀ hn_pos.le hlogN2_ge 3
  · -- second conjunct
    calc ((2:ℝ) ^ (Real.log (2 * Pa.N) / p))^2
        ≤ Real.exp (0.0035 * (1 + n)) := hT_le
      _ ≤ Real.sqrt Pa.N := by
          rw [hsqrt]
          apply Real.exp_le_exp.mpr
          linarith [hn_gt]
      _ ≤ 1.67 * Real.sqrt Pa.N * (Real.log (2 + Pa.N))^3 := by
          have h1 : (1:ℝ) ≤ 1.67 * (Real.log (2 + Pa.N))^3 := by nlinarith [hcube_one]
          calc Real.sqrt Pa.N = Real.sqrt Pa.N * 1 := (mul_one _).symm
            _ ≤ Real.sqrt Pa.N * (1.67 * (Real.log (2 + Pa.N))^3) :=
                mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
            _ = 1.67 * Real.sqrt Pa.N * (Real.log (2 + Pa.N))^3 := by ring

end

end Work.FIArea6
