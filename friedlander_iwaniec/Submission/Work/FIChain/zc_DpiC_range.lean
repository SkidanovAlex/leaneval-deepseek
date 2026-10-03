/-
# `Submission.Work.FIChain.zc_DpiC_range`

The three range facts at the `ρ`-window scale of the FI endgame that the §10 `Π`-removal
consumes (see the handoff comment in `RhoWindowIntegrated2.lean`):

* `DpiC x ≤ x^{3η/32}` — the Rankin threshold `Δπ` is below every fixed positive power of `x`
  (`Work.FIChain.eventually_Dpi_le_rpow` with `κ = 2^{40}`, `r = 3η/32`);
* `⌊zc^{1-η}⌋ ≤ (zc / 2Δπ)^{1-η/4}` — the truncation level sits below the window top after the
  `Δπ`-shift, the exponent `1-η` being compensated by the exponent `1-η/4` and the gap
  `(5/16)(1-η) < (5/16-3η/32)(1-η/4)` of the two exponents (`rpow_gap_mul`);
* `x^{1/4+η/4}+1 < zc/Δπ` — the window bottom clears the box's lower position bound, using
  `zc ≍ x^{5/16}` against `DpiC ≤ x^{3η/32}` and the exponent gap `1/4+η/4 < 5/16-3η/32`
  (`rpow_gap_lt`).

All the `x`-arithmetic is isolated in `rpow_gap_mul` / `rpow_gap_lt`; the sharp size of `zc`
(`x^{5/16}/2 ≤ zc x B ≤ 2x^{5/16}`) is `zc_sharp_bounds`.  This file is complete.
-/
import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.Yc_lower_sharp
import Submission.Work.FIChain.BpWinAux
import Submission.Work.FIChain.zc_sharp_bounds
import Submission.Work.FIChain.rpow_gap_mul
import Submission.Work.FIChain.rpow_gap_lt
import Submission.Work.FITop.RCPrelude

namespace Work.FIChain

open Filter

theorem zc_DpiC_range (η : ℝ) (hη : 0 < η) (hη16 : η < 1 / 32) (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (Work.FIChain.DpiC x : ℝ) ≤ (x : ℝ) ^ (3 * η / 32) ∧
      (((⌊(Work.FIChain.zc x B) ^ (1 - η)⌋₊ : ℕ) : ℝ)) ≤ (Work.FIChain.zc x B / (2 * (Work.FIChain.DpiC x : ℝ))) ^ (1 - η / 4) ∧
      (x : ℝ) ^ ((1 : ℝ) / 4 + η / 4) + 1 < Work.FIChain.zc x B / (Work.FIChain.DpiC x : ℝ) := by
  have _ : (0 : ℝ) < η := hη
  have h1η : (0 : ℝ) < 1 - η := by linarith
  have h1η4 : (0 : ℝ) < 1 - η / 4 := by linarith
  have h3η : (0 : ℝ) < 3 * η / 32 := by positivity
  -- the Rankin threshold is below every fixed positive power of `x`
  have hDpi : ∀ᶠ x : ℕ in Filter.atTop, (Work.FIChain.DpiC x : ℝ) ≤ (x : ℝ) ^ (3 * η / 32) := by
    filter_upwards [Work.FIChain.eventually_Dpi_le_rpow ((2 : ℝ) ^ 40) (3 * η / 32)
      (by positivity) h3η] with x hx
    exact hx
  -- the three scale inputs
  have hzcB := zc_sharp_bounds B hB
  have hgapmul := rpow_gap_mul η hη hη16
  have hgaplt := rpow_gap_lt η hη hη16
  filter_upwards [hDpi, hzcB, hgapmul, hgaplt, eventually_ge_atTop 1]
    with x hDpi hzc hgapmul hgaplt hx1
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hzpos : 0 < Work.FIChain.zc x B := by
    have h5 : 0 < (x : ℝ) ^ ((5 : ℝ) / 16) := Real.rpow_pos_of_pos hxpos _
    linarith [hzc.1, h5]
  have hdpos : 0 < (Work.FIChain.DpiC x : ℝ) := by
    have h : 0 < Work.FIChain.DpiC x := by
      rw [Work.FIChain.DpiC, Work.FIChain.Dpi]
      exact Nat.ceil_pos.mpr (Real.exp_pos _)
    exact_mod_cast h
  refine ⟨hDpi, ?_, ?_⟩
  · -- `⌊zc^{1-η}⌋ ≤ (zc/(2Δπ))^{1-η/4}`
    have hfl : (((⌊(Work.FIChain.zc x B) ^ (1 - η)⌋₊ : ℕ) : ℝ))
        ≤ (Work.FIChain.zc x B) ^ (1 - η) :=
      Nat.floor_le (Real.rpow_nonneg hzpos.le _)
    have h2 : (Work.FIChain.zc x B) ^ (1 - η)
        ≤ (2 * (x : ℝ) ^ ((5 : ℝ) / 16)) ^ (1 - η) :=
      Real.rpow_le_rpow hzpos.le hzc.2 h1η.le
    have hbase : (x : ℝ) ^ ((5 : ℝ) / 16 - 3 * η / 32) / 4
        ≤ Work.FIChain.zc x B / (2 * (Work.FIChain.DpiC x : ℝ)) := by
      have hb : (x : ℝ) ^ ((5 : ℝ) / 16) / 2 / (2 * (x : ℝ) ^ (3 * η / 32))
          ≤ Work.FIChain.zc x B / (2 * (Work.FIChain.DpiC x : ℝ)) :=
        div_le_div₀ hzpos.le hzc.1 (by positivity)
          (by have := mul_le_mul_of_nonneg_left hDpi (by norm_num : (0 : ℝ) ≤ 2); linarith)
      have heq : (x : ℝ) ^ ((5 : ℝ) / 16) / 2 / (2 * (x : ℝ) ^ (3 * η / 32))
          = (x : ℝ) ^ ((5 : ℝ) / 16 - 3 * η / 32) / 4 := by
        rw [show (x : ℝ) ^ ((5 : ℝ) / 16) / 2 / (2 * (x : ℝ) ^ (3 * η / 32))
              = ((x : ℝ) ^ ((5 : ℝ) / 16) / (x : ℝ) ^ (3 * η / 32)) / 4 by ring,
          ← Real.rpow_sub hxpos]
      linarith [hb, heq]
    have h3 : ((x : ℝ) ^ ((5 : ℝ) / 16 - 3 * η / 32) / 4) ^ (1 - η / 4)
        ≤ (Work.FIChain.zc x B / (2 * (Work.FIChain.DpiC x : ℝ))) ^ (1 - η / 4) :=
      Real.rpow_le_rpow (by positivity) hbase h1η4.le
    exact le_trans hfl (le_trans h2 (le_trans hgapmul h3))
  · -- `x^{1/4+η/4}+1 < zc/Δπ`
    have hb : (x : ℝ) ^ ((5 : ℝ) / 16) / 2 / (x : ℝ) ^ (3 * η / 32)
        ≤ Work.FIChain.zc x B / (Work.FIChain.DpiC x : ℝ) :=
      div_le_div₀ hzpos.le hzc.1 hdpos hDpi
    have heq : (x : ℝ) ^ ((5 : ℝ) / 16) / 2 / (x : ℝ) ^ (3 * η / 32)
        = (x : ℝ) ^ ((5 : ℝ) / 16 - 3 * η / 32) / 2 := by
      rw [show (x : ℝ) ^ ((5 : ℝ) / 16) / 2 / (x : ℝ) ^ (3 * η / 32)
            = ((x : ℝ) ^ ((5 : ℝ) / 16) / (x : ℝ) ^ (3 * η / 32)) / 2 by ring,
          ← Real.rpow_sub hxpos]
    exact lt_of_lt_of_le hgaplt (le_trans (le_of_eq heq.symm) hb)

end Work.FIChain
