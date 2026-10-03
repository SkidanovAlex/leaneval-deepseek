/-
# `Submission.Work.FIArea6T.LogArith` — the elementary real arithmetic of the τ-removal

The τ-removal of *FI* (10.4) multiplies three bounds:

* the Schur factor `θN log²(2+N)` of T2 (`Work.FIArea6T.TcutBil_le_polar`);
* the clean second moment `√(N log⁷(2+N))` of T3 (`Work.FIArea6T.cleanCoeff_sq_mass_le`);
* the Mass of the (5.9)-complement `√N (log N)^{-2·10^9}` of T4
  (`Work.FIArea6T.cleanTau_mass_le`),

and asks the product to be at most `N²(log N)^{-19·10^8}`.  With `θ ≤ 1` this is the chain

  `log²(2+N)·log⁷ᐟ²(2+N) = log⁶(2+N) ≤ (1+log 3)⁶ log⁶ N`

and then `log⁶N · (log N)^{-2·10^9} ≤ (log N)^{-19·10^8}`, whose exponent deficit
`2·10^9 − 19·10^8 = 10^8` is enormous compared with the power `6` consumed.

This module collects those inequalities, together with the threshold facts about `Pa.x`, `Pa.N`
and `log Pa.N` that the τ-removal needs (`Pa.x ≥ exp 12` gives `3 ≤ Pa.N` and `1 ≤ log Pa.N`).
-/
import Mathlib
import Submission.Work.FIArea6T.Defs
import Submission.Work.FIArea6T.Support

set_option autoImplicit false

namespace Work.FIArea6T

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 1. `log(2+N)` versus `log N` -/

/-- For `N ≥ 1` with `1 ≤ log N`, `log(2 + N) ≤ (1 + log 3)·log N` (since `2 + N ≤ 3N`). -/
lemma log_two_add_le {N : ℝ} (hN : 1 ≤ N) (hL : 1 ≤ Real.log N) :
    Real.log (2 + N) ≤ (1 + Real.log 3) * Real.log N := by
  have hpos : (0 : ℝ) < 2 + N := by linarith
  have h3N : 2 + N ≤ 3 * N := by linarith
  have hlog : Real.log (2 + N) ≤ Real.log (3 * N) := Real.log_le_log hpos h3N
  have h3 : Real.log (3 * N) = Real.log 3 + Real.log N :=
    Real.log_mul (by norm_num) (by linarith)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  rw [h3] at hlog
  nlinarith [hlog, hlog3, hL]

/-! ## 2. The two square-root bounds -/

/-- `√(N·L^{-4·10^9}) ≤ √N·L^{-2·10^9}` for `L ≥ 0`. -/
lemma sqrt_mass_le {N L : ℝ} (hN : 0 ≤ N) (hL : 0 ≤ L) :
    Real.sqrt (N * L ^ (-(4 * 10 ^ 9 : ℝ)))
      ≤ Real.sqrt N * L ^ (-(2 * 10 ^ 9 : ℝ)) := by
  rcases eq_or_lt_of_le hL with hL0 | hLpos
  · rw [← hL0, Real.zero_rpow (by norm_num : (-(4 * 10 ^ 9 : ℝ)) ≠ 0), mul_zero, Real.sqrt_zero,
      Real.zero_rpow (by norm_num : (-(2 * 10 ^ 9 : ℝ)) ≠ 0), mul_zero]
  · have hsq : L ^ (-(4 * 10 ^ 9 : ℝ)) = (L ^ (-(2 * 10 ^ 9 : ℝ))) ^ 2 := by
      rw [sq, ← Real.rpow_add hLpos]
      congr 1
      norm_num
    rw [hsq, Real.sqrt_mul hN, Real.sqrt_sq (Real.rpow_nonneg hL _)]

/-- `√(C·N·L⁷) ≤ √C·√N·L⁴` for `C, N ≥ 0` and `L ≥ 1`. -/
lemma sqrt_sq_mass_le {C N L : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N) (hL : 1 ≤ L) :
    Real.sqrt (C * N * L ^ 7) ≤ Real.sqrt C * Real.sqrt N * L ^ 4 := by
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have h7 : Real.sqrt (L ^ 7) ≤ L ^ 4 := by
    have h78 : L ^ 7 ≤ (L ^ 4) ^ 2 := by
      have h := pow_le_pow_right₀ hL (show 7 ≤ 8 by norm_num)
      have h2 : L ^ 8 = (L ^ 4) ^ 2 := by ring
      rwa [h2] at h
    have := Real.sqrt_le_sqrt h78
    rwa [Real.sqrt_sq (by positivity)] at this
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ C * N), Real.sqrt_mul hC]
  have hnn : (0 : ℝ) ≤ Real.sqrt C * Real.sqrt N := by positivity
  calc Real.sqrt C * Real.sqrt N * Real.sqrt (L ^ 7)
      ≤ Real.sqrt C * Real.sqrt N * L ^ 4 := mul_le_mul_of_nonneg_left h7 hnn

/-- `L^k · L^c ≤ L^{c'}` for `L ≥ 1` and `k + c ≤ c'`. -/
lemma pow_mul_rpow_le {L : ℝ} (hL : 1 ≤ L) (k : ℕ) {c c' : ℝ} (h : (k : ℝ) + c ≤ c') :
    L ^ k * L ^ c ≤ L ^ c' := by
  have hL0 : (0 : ℝ) < L := by linarith
  rw [← Real.rpow_natCast (x := L) k, ← Real.rpow_add hL0]
  exact Real.rpow_le_rpow_of_exponent_le hL h

/-- The exponent bookkeeping of the τ-removal: `log⁶N · (log N)^{-2·10^9} ≤ (log N)^{-19·10^8}`
for `1 ≤ log N` (the deficit `10^8` dwarfs the power `6`). -/
lemma rpow_six_mul_le {L : ℝ} (hL : 1 ≤ L) :
    L ^ 6 * L ^ (-(2 * 10 ^ 9 : ℝ)) ≤ L ^ (-(19 * 10 ^ 8 : ℝ)) := by
  refine pow_mul_rpow_le hL 6 (c := -(2 * 10 ^ 9 : ℝ)) (c' := -(19 * 10 ^ 8 : ℝ)) ?_
  norm_num

/-! ## 3. The threshold facts of `Params` at `x ≥ exp 12` -/

/-- At `Pa.x ≥ exp 12` one has `x ≥ 1` and `log x ≥ 12`. -/
lemma threshold_log {Pa : Work.FITop.Params} (hx : Real.exp 12 ≤ (Pa.x : ℝ)) :
    (1 : ℝ) ≤ (Pa.x : ℝ) ∧ 12 ≤ Real.log (Pa.x : ℝ) := by
  have h1 : (1 : ℝ) ≤ Real.exp 12 := Real.one_le_exp (by norm_num)
  refine ⟨le_trans h1 hx, ?_⟩
  have h := Real.log_le_log (Real.exp_pos 12) hx
  rwa [Real.log_exp] at h

/-- At `Pa.x ≥ exp 12` one has `3 ≤ Pa.N` (since `N > x^{1/4} ≥ e³ > 3`). -/
lemma threshold_N3 {Pa : Work.FITop.Params} (hx : Real.exp 12 ≤ (Pa.x : ℝ)) : 3 ≤ Pa.N := by
  obtain ⟨hx1, -⟩ := threshold_log hx
  have hexp : (Real.exp 12) ^ ((1 : ℝ) / 4) = Real.exp 3 := by
    rw [← Real.exp_mul]
    norm_num
  have hxpow : Real.exp 3 ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← hexp]
    exact Real.rpow_le_rpow (Real.exp_pos 12).le hx (by norm_num)
  have hexp3 : (3 : ℝ) < Real.exp 3 := by
    have h := Real.add_one_le_exp (3 : ℝ)
    linarith
  have hexpη : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) := by
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    linarith [Pa.hη]
  have hlt : (3 : ℝ) < Pa.N := by
    have h1 : Real.exp 3 < Pa.N := lt_of_le_of_lt (le_trans hxpow hexpη) Pa.hNlo
    exact lt_of_lt_of_le hexp3 (le_of_lt h1)
  exact_mod_cast le_of_lt hlt

/-- At `Pa.x ≥ exp 12` one has `1 ≤ log Pa.N` (indeed `log N ≥ (1/4)·log x ≥ 3`). -/
lemma threshold_logN {Pa : Work.FITop.Params} (hx : Real.exp 12 ≤ (Pa.x : ℝ)) :
    1 ≤ Real.log Pa.N := by
  obtain ⟨hx1, hx12⟩ := threshold_log hx
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by linarith
  have hpowpos : (0 : ℝ) < (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hxpos _
  have hle : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ Pa.N :=
    le_of_lt (lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [Pa.hη])) Pa.hNlo)
  have hlog : Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 4)) ≤ Real.log Pa.N :=
    Real.log_le_log hpowpos hle
  rw [Real.log_rpow hxpos] at hlog
  have : (3 : ℝ) ≤ Real.log Pa.N := by nlinarith [hlog, hx12]
  linarith

/-- `N ≥ 3` also gives `log 3 ≤ log N`. -/
lemma log_three_le_log_N {N : ℝ} (hN : 3 ≤ N) : Real.log 3 ≤ Real.log N :=
  Real.log_le_log (by norm_num) hN

/-! ## 4. The final multiplicative assembly -/

/-- `1 ≤ log(2+N)` for `N ≥ 3`. -/
lemma log_two_add_ge_one {N : ℝ} (hN : 3 ≤ N) : 1 ≤ Real.log (2 + N) := by
  have h : (3 : ℝ) ≤ 2 + N := by linarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3) h
  have h2 : (1 : ℝ) < Real.log 3 := by
    have hh := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    rwa [Real.log_exp] at hh
  linarith

/-- `θ·L⁶·M^{-2·10^9} ≤ (1+log 3)⁶·M^{-19·10^8}` for `0 ≤ θ ≤ 1`, `M ≥ 1` and
`L⁶ ≤ (1+log 3)⁶M⁶` (so `L` is `log(2+N)` and `M ≥ log N`). -/
lemma theta_mul_pow_rpow_le (θ L M : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hL0 : 0 ≤ L)
    (hM1 : 1 ≤ M) (hL6 : L ^ 6 ≤ (1 + Real.log 3) ^ 6 * M ^ 6) :
    θ * L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ)) ≤ (1 + Real.log 3) ^ 6 * M ^ (-(19 * 10 ^ 8 : ℝ)) := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hr : (0 : ℝ) ≤ M ^ (-(2 * 10 ^ 9 : ℝ)) := Real.rpow_nonneg hM0.le _
  have hMr : M ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ)) ≤ M ^ (-(19 * 10 ^ 8 : ℝ)) :=
    pow_mul_rpow_le hM1 6 (by norm_num)
  have hstep1 : θ * L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ)) ≤ L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ)) := by
    calc θ * L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ))
        = θ * (L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ))) := by ring
      _ ≤ 1 * (L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ))) :=
          mul_le_mul_of_nonneg_right hθ1 (mul_nonneg (pow_nonneg hL0 6) hr)
      _ = L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ)) := by ring
  have hstep2 : L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ))
      ≤ ((1 + Real.log 3) ^ 6 * M ^ 6) * M ^ (-(2 * 10 ^ 9 : ℝ)) :=
    mul_le_mul_of_nonneg_right hL6 hr
  have hstep3 : ((1 + Real.log 3) ^ 6 * M ^ 6) * M ^ (-(2 * 10 ^ 9 : ℝ))
      = (1 + Real.log 3) ^ 6 * (M ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ))) := by ring
  calc θ * L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ)) ≤ L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ)) := hstep1
    _ ≤ ((1 + Real.log 3) ^ 6 * M ^ 6) * M ^ (-(2 * 10 ^ 9 : ℝ)) := hstep2
    _ = (1 + Real.log 3) ^ 6 * (M ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ))) := hstep3
    _ ≤ (1 + Real.log 3) ^ 6 * M ^ (-(19 * 10 ^ 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left hMr (by positivity)

/-- **The final product of the τ-removal.**  Multiplying the Schur factor `θN L²`, the clean second
moment `√C₃√N L⁴` and the complement mass `√N M^{-2·10^9}` gives at most
`3·10⁴√C₃(1+log 3)⁶N²M^{-19·10^8}`. -/
lemma tau_arith_final (C3 θ N L M : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hN0 : 0 ≤ N)
    (hθL : θ * L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ))
      ≤ (1 + Real.log 3) ^ 6 * M ^ (-(19 * 10 ^ 8 : ℝ))) :
    3 * (10 ^ 4 * θ * N * L ^ 2) * (Real.sqrt C3 * Real.sqrt N * L ^ 4)
        * (Real.sqrt N * M ^ (-(2 * 10 ^ 9 : ℝ)))
      ≤ 3 * 10 ^ 4 * Real.sqrt C3 * (1 + Real.log 3) ^ 6 * N ^ 2
          * M ^ (-(19 * 10 ^ 8 : ℝ)) := by
  have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0
  have hC30 : (0 : ℝ) ≤ Real.sqrt C3 := Real.sqrt_nonneg _
  calc 3 * (10 ^ 4 * θ * N * L ^ 2) * (Real.sqrt C3 * Real.sqrt N * L ^ 4)
        * (Real.sqrt N * M ^ (-(2 * 10 ^ 9 : ℝ)))
      = (Real.sqrt N * Real.sqrt N) * (3 * 10 ^ 4 * Real.sqrt C3 * N)
          * (θ * L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ))) := by ring
    _ = N * (3 * 10 ^ 4 * Real.sqrt C3 * N)
          * (θ * L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ))) := by rw [hsqN]
    _ = (3 * 10 ^ 4 * Real.sqrt C3 * N ^ 2)
          * (θ * L ^ 6 * M ^ (-(2 * 10 ^ 9 : ℝ))) := by ring
    _ ≤ (3 * 10 ^ 4 * Real.sqrt C3 * N ^ 2)
          * ((1 + Real.log 3) ^ 6 * M ^ (-(19 * 10 ^ 8 : ℝ))) :=
        mul_le_mul_of_nonneg_left hθL (by positivity)
    _ = 3 * 10 ^ 4 * Real.sqrt C3 * (1 + Real.log 3) ^ 6 * N ^ 2
          * M ^ (-(19 * 10 ^ 8 : ℝ)) := by ring

/-- The same, with `L = log(2+N)`, `M = log N` and the consequences of `log(2+N) ≤ (1+log 3)log N`. -/
lemma tau_arith_log (C3 θ N : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hN0 : 0 ≤ N)
    (hL1 : 1 ≤ Real.log (2 + N)) (hM1 : 1 ≤ Real.log N)
    (hLM : Real.log (2 + N) ≤ (1 + Real.log 3) * Real.log N) :
    3 * (10 ^ 4 * θ * N * (Real.log (2 + N)) ^ 2)
        * (Real.sqrt C3 * Real.sqrt N * (Real.log (2 + N)) ^ 4)
        * (Real.sqrt N * (Real.log N) ^ (-(2 * 10 ^ 9 : ℝ)))
      ≤ 3 * 10 ^ 4 * Real.sqrt C3 * (1 + Real.log 3) ^ 6 * N ^ 2
          * (Real.log N) ^ (-(19 * 10 ^ 8 : ℝ)) := by
  have hL0 : (0 : ℝ) ≤ Real.log (2 + N) := by linarith
  have hL6 : (Real.log (2 + N)) ^ 6 ≤ (1 + Real.log 3) ^ 6 * (Real.log N) ^ 6 := by
    have h1 : (Real.log (2 + N)) ^ 6 ≤ ((1 + Real.log 3) * Real.log N) ^ 6 :=
      pow_le_pow_left₀ hL0 hLM 6
    rwa [mul_pow] at h1
  exact tau_arith_final C3 θ N (Real.log (2 + N)) (Real.log N) hθ0 hθ1 hN0
    (theta_mul_pow_rpow_le θ (Real.log (2 + N)) (Real.log N) hθ0 hθ1 hL0 hM1 hL6)

end

end Work.FIArea6T
