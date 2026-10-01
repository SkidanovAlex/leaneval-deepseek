import Mathlib
import Submission.Work.LinnikAreas.DhRepel.rpowArithLogFree
import Submission.Work.LinnikAreas.DhRepel.rpowBaseLeLogLogPow
import Submission.Work.LinnikAreas.DhRepel.eventuallyMulLogPowLeRpow

namespace Work.ZeroFreeTables

open Work.LinnikAreas.DhRepel (rpowBaseLeLogLogPow eventuallyMulLogPowLeRpow)

/-- **The `4 t` variant of `rpowBaseLeLogLogPow`.**

For `q` with `L := log q ≥ 100` and `t ≥ 0` with `3 t ≤ log (log (log q))`, the real power
`(q * (10 * log q)) ^ (4 t / log q)` is at most `(log (log q)) ^ 15`.

Write `L = log q`, `K = log (log q)`.  Since
`4 t / L = (3 t / L) * (4 / 3)`, the quantity on the left is the `4 / 3`-th power of
`(q * 10 L) ^ (3 t / L)`.  By `rpowBaseLeLogLogPow` the latter is at most `K ^ 11`, whence
`(q * 10 L) ^ (4 t / L) ≤ (K ^ 11) ^ (4 / 3) = K ^ (44 / 3) ≤ K ^ 15`, because `K ≥ 1`
(here `K ≥ log 100 ≥ 1`). -/
theorem rpowBaseLeLogLogPow4 (q : ℕ) (t : ℝ)
    (hL : 100 ≤ Real.log (q : ℝ)) (ht0 : 0 ≤ t)
    (htZ : 3 * t ≤ Real.log (Real.log (Real.log (q : ℝ)))) :
    ((q : ℝ) * (10 * Real.log (q : ℝ))) ^ (4 * t / Real.log (q : ℝ))
      ≤ (Real.log (Real.log (q : ℝ))) ^ 15 := by
  have hLpos : 0 < Real.log (q : ℝ) := by linarith
  have hqne : (q : ℝ) ≠ 0 := by
    intro h
    have hzero : Real.log (q : ℝ) = 0 := by rw [h, Real.log_zero]
    linarith
  have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg q) (Ne.symm hqne)
  have hbasepos : 0 < (q : ℝ) * (10 * Real.log (q : ℝ)) :=
    mul_pos hqpos (by linarith)
  -- `K := log (log q) ≥ log 100 ≥ 1`
  have hKge : 1 ≤ Real.log (Real.log (q : ℝ)) := by
    have h100 : (1 : ℝ) ≤ Real.log 100 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_three]
    have hle : Real.log 100 ≤ Real.log (Real.log (q : ℝ)) :=
      Real.log_le_log (by norm_num) hL
    linarith
  have hKlpos : 0 < Real.log (Real.log (q : ℝ)) := lt_of_lt_of_le one_pos hKge
  -- the `3 t` bound
  have h3 : ((q : ℝ) * (10 * Real.log (q : ℝ))) ^ (3 * t / Real.log (q : ℝ))
      ≤ (Real.log (Real.log (q : ℝ))) ^ 11 :=
    rpowBaseLeLogLogPow q t hL ht0 htZ
  -- the same bound with the right-hand side written as a real power
  have h3r : ((q : ℝ) * (10 * Real.log (q : ℝ))) ^ (3 * t / Real.log (q : ℝ))
      ≤ (Real.log (Real.log (q : ℝ))) ^ ((11 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact h3
  -- `4 t / L = (3 t / L) * (4 / 3)`
  have hfe : 4 * t / Real.log (q : ℝ)
      = (3 * t / Real.log (q : ℝ)) * (4 / 3) := by ring
  rw [hfe, Real.rpow_mul (le_of_lt hbasepos)]
  -- now bound by the `3 t` estimate and compare exponents
  refine le_trans
    (Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hbasepos) _) h3r (by norm_num)) ?_
  have h15 : (Real.log (Real.log (q : ℝ))) ^ 15
      = (Real.log (Real.log (q : ℝ))) ^ ((15 : ℕ) : ℝ) :=
    (Real.rpow_natCast _ 15).symm
  rw [h15, ← Real.rpow_mul (le_of_lt hKlpos)]
  exact Real.rpow_le_rpow_of_exponent_le hKge (by norm_num)

/-- **Log-free arithmetic estimate (`4 t` form).**  For all `C > 0` and `A > 0` there is `q₀` such
that for every `q ≥ q₀` and every `t` with `0 ≤ t ≤ (1/3) log log log q`,

  `C · (q · 10 log q)^{4t/log q} ≤ (log q)^A`.

Since `4t ≤ (4/3) log log log q`, the power is at most `(log log q)^15`
(`rpowBaseLeLogLogPow4`), and a polynomial in `log log q` is eventually dominated by `(log q)^A`
for every `A > 0` (`eventuallyMulLogPowLeRpow`). -/
theorem t23ArithFour (C A : ℝ) (hC : 0 < C) (hA : 0 < A) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ t : ℝ, 0 ≤ t →
      t ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
      C * ((q : ℝ) * (10 * Real.log (q : ℝ))) ^ (4 * t / Real.log (q : ℝ))
        ≤ (Real.log (q : ℝ)) ^ A := by
  -- `log q → ∞`, so eventually `log q ≥ 100`
  have hlog : ∀ᶠ q : ℕ in Filter.atTop, 100 ≤ Real.log (q : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 100)
  -- `log`-powers are eventually dominated by any positive power
  have hdom : ∀ᶠ q : ℕ in Filter.atTop,
      C * (Real.log (Real.log (q : ℝ))) ^ 15 ≤ (Real.log (q : ℝ)) ^ A :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventuallyMulLogPowLeRpow C A 15 hC hA)
  -- combine the two eventual statements into a single threshold
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (hlog.and hdom)
  refine ⟨q₀, fun q hq t ht0 htle => ?_⟩
  obtain ⟨hL, hdomq⟩ := hq₀ q hq
  -- the hypothesis `t ≤ (1/3) log log log q` gives `3t ≤ log log log q`
  have htZ : 3 * t ≤ Real.log (Real.log (Real.log (q : ℝ))) := by linarith
  -- the pure power bound
  have hpow := rpowBaseLeLogLogPow4 q t hL ht0 htZ
  calc C * ((q : ℝ) * (10 * Real.log (q : ℝ))) ^ (4 * t / Real.log (q : ℝ))
      ≤ C * (Real.log (Real.log (q : ℝ))) ^ 15 :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
    _ ≤ (Real.log (q : ℝ)) ^ A := hdomq

end Work.ZeroFreeTables
