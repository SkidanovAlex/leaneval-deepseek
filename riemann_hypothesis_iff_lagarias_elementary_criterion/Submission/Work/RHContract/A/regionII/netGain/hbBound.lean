import Mathlib
import Submission.Work.RHContract.A.regionII.caNet2_defs

/-!
# `Work.RHContract.A.regionII.netGain.hbBound`

The elementary bound dominating the `Net₂` summand `1/(2p(p−1))` by the linear weight
`netHb ξ · log p` on the *gain region* `p > netPf ξ = ⌊1.15√ξ⌋₊`.

Writing `s = √ξ` (so `ξ = s²` and `log ξ = 2 log s`), for `ξ ∈ [10⁵, 10⁸)` we have
`s ≥ 316`, and `netHb ξ = (38/100)/(s²·(log s + 1397/10000))`.  If the prime `p`
exceeds `⌊1.15√ξ⌋₊` then `p > 1.15 s`, so

* `log p > log(1.15 s) = log(1.15) + log s ≥ 1397/10000 + log s`, and
* `2p(p−1) ≥ 2·(1.15 s)(1.15 s − 1)`, whence `1/(2p(p−1)) ≤ 38/100/s²`
  (which reduces to `0.0051 s² ≥ 0.874 s`, true since `s ≥ 316`).

Combining the two gives the claim.  This file is the numerical input to the
`Net₂ ≥ 0` estimate in Region II.
-/

namespace Work.RHContract.A.regionII.netGain

theorem hbBound (ξ : ℝ) (hlo : (100000 : ℝ) ≤ ξ) (hhi : ξ < (10 : ℝ) ^ 8) :
    ∀ p : ℕ, netPf ξ < p →
      1 / (2 * (p : ℝ) * ((p : ℝ) - 1)) ≤ netHb ξ * Real.log (p : ℝ) := by
  intro p hp
  have hξpos : 0 < ξ := by linarith
  set s : ℝ := Real.sqrt ξ with hsdef
  have hspos : 0 < s := by
    rw [hsdef]; exact Real.sqrt_pos.mpr hξpos
  have hs316 : 316 ≤ s := by
    rw [hsdef]
    have h1 : (316 : ℝ) ≤ Real.sqrt 100000 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    exact le_trans h1 (Real.sqrt_le_sqrt hlo)
  have hs1 : 1 < s := by linarith
  have hlogspos : 0 < Real.log s := Real.log_pos hs1
  have hssq : s ^ 2 = ξ := by
    rw [hsdef]; exact Real.sq_sqrt (le_of_lt hξpos)
  have hlog : Real.log ξ = 2 * Real.log s := by
    have h := Real.log_sqrt (le_of_lt hξpos)
    rw [← hsdef] at h
    linarith
  -- `p` lies strictly above the cut `⌊1.15 √ξ⌋₊`, hence above `1.15 s`
  have hpA : (115 / 100 * s : ℝ) < (p : ℝ) := by
    have hPf : netPf ξ = ⌊(115 / 100) * s⌋₊ := by
      unfold netPf
      rw [← hsdef]
    have h1 : ⌊(115 / 100) * s⌋₊ + 1 ≤ p := by
      have h2 : netPf ξ + 1 ≤ p := Nat.succ_le_of_lt hp
      rwa [hPf] at h2
    have hple : ((⌊(115 / 100) * s⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast h1
    have hlt := Nat.lt_floor_add_one ((115 / 100) * s)
    linarith
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith [hpA, hs316]
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith [hpA, hs316]
  have hA1pos : (0 : ℝ) < 115 / 100 * s - 1 := by linarith [hs316]
  -- Step 1: replace `p` by the (smaller) real number `1.15 s`
  have hstep1 : 1 / (2 * (p : ℝ) * ((p : ℝ) - 1))
      ≤ 1 / (2 * (115 / 100 * s) * (115 / 100 * s - 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hprod : (115 / 100 * s) * (115 / 100 * s - 1) ≤ (p : ℝ) * ((p : ℝ) - 1) :=
      mul_le_mul (le_of_lt hpA) (by linarith) (le_of_lt hA1pos) (le_of_lt hp_pos)
    linarith
  -- Step 2: the numerical core, `1/(2·(1.15 s)(1.15 s − 1)) ≤ (38/100)/s²`
  have hstep2 : 1 / (2 * (115 / 100 * s) * (115 / 100 * s - 1)) ≤ 38 / 100 / s ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hs316]
  -- Step 3: `log p` dominates the constant `log s + 0.1397` inside the weight
  have hstep3 : 38 / 100 / s ^ 2
      ≤ 38 / 100 / (s ^ 2 * (Real.log s + 1397 / 10000)) * Real.log (p : ℝ) := by
    have hlogp : Real.log s + 1397 / 10000 ≤ Real.log (p : ℝ) := by
      have h1 : Real.log (115 / 100 * s) = Real.log (115 / 100) + Real.log s :=
        Real.log_mul (by norm_num) (ne_of_gt hspos)
      have h2 : Real.log (115 / 100 * s) < Real.log (p : ℝ) :=
        Real.log_lt_log (by positivity) hpA
      have h3 : (1397 / 10000 : ℝ) ≤ Real.log (115 / 100) := net_log_115_ge
      linarith
    have hBpos : 0 < Real.log s + 1397 / 10000 := by linarith
    have hcoefpos : 0 < 38 / 100 / (s ^ 2 * (Real.log s + 1397 / 10000)) := by positivity
    have hmono := mul_le_mul_of_nonneg_left hlogp (le_of_lt hcoefpos)
    have heq : (38 / 100 : ℝ) / s ^ 2
        = 38 / 100 / (s ^ 2 * (Real.log s + 1397 / 10000)) * (Real.log s + 1397 / 10000) := by
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ (ne_of_gt hBpos)]
    linarith
  -- rewrite `netHb ξ` in terms of `s`
  have hHb : netHb ξ = 38 / 100 / (s ^ 2 * (Real.log s + 1397 / 10000)) := by
    have hden : ξ * (Real.log ξ / 2 + 1397 / 10000) = s ^ 2 * (Real.log s + 1397 / 10000) := by
      rw [hlog, ← hssq]; ring
    rw [netHb, hden]
  rw [hHb]
  linarith [hstep1, hstep2, hstep3]

end Work.RHContract.A.regionII.netGain
