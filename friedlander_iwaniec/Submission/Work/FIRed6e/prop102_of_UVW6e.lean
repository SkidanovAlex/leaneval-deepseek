/-
# `Submission.Work.FIRed6e.prop102_of_UVW6e` — Proposition 10.2 with the τ-removal slot

Node C2 of the amended composition (design `Submission/Work/FIArea6/AREA6_CONTRACT_LEAD.md` §4.1):
the assembled Proposition 10.2 bound

  `‖T(β)‖ ≤ (cU+cV+cW+cE)·(N²(log N)^{-σ} + P^{-1}N²log N)`,

i.e. `Submission.Work.FITop4.Red6.prop102_of_UVW6` with one extra summand
`cE·N²(log N)^{-σ}` in the `U`-estimate.  That summand is the slot in which the composition pays the
(5.9) τ-removal `Work.FITop4.TauRemoval6` (FI (10.4)): the piece coefficient supplied by the
reduction carries (5.9), the clean area 6 does not, and the difference costs `N²(log N)^{-19·10^8}`,
which is below the (5.25) budget `N²(log N)^{-σ}`.

The file is the proved `prop102_of_UVW6` verbatim, with `cE` added to the coefficient list, to the
`U`-hypothesis and to the final constant; the two proof steps that see the new summand are the last
two lines of the `calc`.
-/
import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FITop4.Areas6

set_option autoImplicit false

namespace Work.FIRed6e

open scoped BigOperators

/-! ## Auxiliary real-variable lemmas -/

/-- `N ≥ 3` implies `log N ≥ 1` (since `e < 3`). -/
private lemma one_le_log_of_three_le {N : ℝ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hlog3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt h3).mpr Real.exp_one_lt_three
  have hle : Real.log 3 ≤ Real.log N := Real.log_le_log h3 hN
  linarith

/-- If `L ≥ 1`, `σ > 0` and `X ≥ L^{1+σ}` then `X⁻¹·L ≤ L^{-σ}`.

This is the estimate that turns the `1/X` error of the `U`- and `W`-cuts (which carry a factor
`log N`) into the main-term shape `L^{-σ}`. -/
private lemma inv_mul_le_rpow_neg {L X σ : ℝ} (hL1 : 1 ≤ L)
    (hX : L ^ (1 + σ) ≤ X) : X⁻¹ * L ≤ L ^ (-σ) := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hXpos : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos hLpos _) hX
  have hLσpos : 0 < L ^ σ := Real.rpow_pos_of_pos hLpos σ
  have hEq : L ^ (1 + σ) = L * L ^ σ := by rw [Real.rpow_add hLpos, Real.rpow_one]
  have hLmul : L * L ^ σ ≤ X := by rw [← hEq]; exact hX
  have hZ : (X * L ^ (-σ)) * L ^ σ = X := by
    rw [Real.rpow_neg hL0, mul_assoc, inv_mul_cancel₀ (ne_of_gt hLσpos), mul_one]
  have hle : L ≤ X * L ^ (-σ) := (mul_le_mul_iff_left₀ hLσpos).mp (by rw [hZ]; exact hLmul)
  calc X⁻¹ * L ≤ X⁻¹ * (X * L ^ (-σ)) := mul_le_mul_of_nonneg_left hle (le_of_lt (inv_pos.mpr hXpos))
    _ = L ^ (-σ) := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hXpos), one_mul]

/-- If `L ≥ 1`, `σ > 0` and `X ≥ L^{3σ}` then `X^{-1/3} ≤ L^{-σ}`.

This is the estimate for the `V`-cut error term `X^{-1/3}`. -/
private lemma rpow_neg_third_le_rpow_neg {L X σ : ℝ} (hL1 : 1 ≤ L)
    (hX : L ^ (3 * σ) ≤ X) : X ^ (-(1 : ℝ) / 3) ≤ L ^ (-σ) := by
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hL3nn : 0 ≤ L ^ (3 * σ) := Real.rpow_nonneg hL0 _
  have h13 : (0 : ℝ) ≤ (1 : ℝ) / 3 := by norm_num
  have hstep : (L ^ (3 * σ)) ^ ((1 : ℝ) / 3) ≤ X ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hL3nn hX h13
  have hmul : (L ^ (3 * σ)) ^ ((1 : ℝ) / 3) = L ^ σ := by
    rw [← Real.rpow_mul hL0 (3 * σ) ((1 : ℝ) / 3)]
    congr 1
    ring
  have hs : L ^ σ ≤ X ^ ((1 : ℝ) / 3) := by rw [← hmul]; exact hstep
  have hXpos : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos hLpos _) hX
  have hX13pos : 0 < X ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hXpos _
  have hLσpos : 0 < L ^ σ := Real.rpow_pos_of_pos hLpos σ
  have hn : (-(1 : ℝ)) / 3 = -((1 : ℝ) / 3) := by norm_num
  rw [hn, Real.rpow_neg hXpos.le, Real.rpow_neg hL0]
  exact (inv_le_inv₀ hX13pos hLσpos).mpr hs

/-! ## Proposition 10.2 -/

theorem prop102_of_UVW6e (Pa : Work.FITop.Params) (X : ℕ) (σ : ℝ) (β : GaussianInt → ℂ)
    (hσ : 0 < σ) (hN : 3 ≤ Pa.N) (hX : (Real.log Pa.N) ^ (3 * σ + 3) ≤ (X : ℝ))
    (hT : Work.FITop4.Tbeta (Work.FITop.radN Pa) β
      = Work.FITop4.Ucut (Work.FITop.radN Pa) X β + Work.FITop4.Vcut (Work.FITop.radN Pa) X β
        + Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β)
    (cU cV cW cE : ℝ) (hcU : 0 ≤ cU) (hcV : 0 ≤ cV) (hcW : 0 ≤ cW) (hcE : 0 ≤ cE)
    (hU : ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X β‖
        ≤ cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
          + cE * Pa.N ^ 2 * (Real.log Pa.N) ^ (-σ))
    (hV : ‖Work.FITop4.Vcut (Work.FITop.radN Pa) X β‖
        ≤ cV * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ) ^ (-(1 : ℝ) / 3)) * Pa.N ^ 2)
    (hW : ‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖
        ≤ cW * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N) :
    ‖Work.FITop4.Tbeta (Work.FITop.radN Pa) β‖
      ≤ (cU + cV + cW + cE) * (Pa.N ^ 2 * (Real.log Pa.N) ^ (-σ)
          + (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N) := by
  have hL1 : 1 ≤ Real.log Pa.N := one_le_log_of_three_le hN
  have hLpos : 0 < Real.log Pa.N := lt_of_lt_of_le zero_lt_one hL1
  have hN2nn : 0 ≤ Pa.N ^ 2 := by positivity
  have hYnn : 0 ≤ (Pa.Pz : ℝ)⁻¹ := by positivity
  -- the two truncation estimates coming from `X ≥ (log N)^{3σ+3}`
  have hXiL : (X : ℝ)⁻¹ * Real.log Pa.N ≤ (Real.log Pa.N) ^ (-σ) :=
    inv_mul_le_rpow_neg hL1
      (le_trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hX)
  have hXtL : (X : ℝ) ^ (-(1 : ℝ) / 3) ≤ (Real.log Pa.N) ^ (-σ) :=
    rpow_neg_third_le_rpow_neg hL1
      (le_trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hX)
  -- `1/P·N² ≤ 1/P·N²·log N`, since `log N ≥ 1`
  have hYN : (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 ≤ (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N :=
    le_mul_of_one_le_right (mul_nonneg hYnn hN2nn) hL1
  -- the three per-cut bounds, each replaced by `correct main term + error term`
  have hU' : cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
      ≤ cU * (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N
        + cU * Pa.N ^ 2 * (Real.log Pa.N) ^ (-σ) := by
    have h1 : cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
        = cU * (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N
          + cU * Pa.N ^ 2 * ((X : ℝ)⁻¹ * Real.log Pa.N) := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hXiL (mul_nonneg hcU hN2nn)
    linarith
  have hV' : cV * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ) ^ (-(1 : ℝ) / 3)) * Pa.N ^ 2
      ≤ cV * (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N
        + cV * Pa.N ^ 2 * (Real.log Pa.N) ^ (-σ) := by
    have h1 : cV * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ) ^ (-(1 : ℝ) / 3)) * Pa.N ^ 2
        = cV * (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 + cV * Pa.N ^ 2 * (X : ℝ) ^ (-(1 : ℝ) / 3) := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hYN hcV
    have h3 := mul_le_mul_of_nonneg_left hXtL (mul_nonneg hcV hN2nn)
    linarith
  have hW' : cW * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
      ≤ cW * (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N
        + cW * Pa.N ^ 2 * (Real.log Pa.N) ^ (-σ) := by
    have h1 : cW * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
        = cW * (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N
          + cW * Pa.N ^ 2 * ((X : ℝ)⁻¹ * Real.log Pa.N) := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hXiL (mul_nonneg hcW hN2nn)
    linarith
  -- regroup `U + V + W + B` as `U + V + (W + B)` to use the `W + B` estimate
  have hgrp : Work.FITop4.Ucut (Work.FITop.radN Pa) X β + Work.FITop4.Vcut (Work.FITop.radN Pa) X β
      + Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β
      = Work.FITop4.Ucut (Work.FITop.radN Pa) X β + Work.FITop4.Vcut (Work.FITop.radN Pa) X β
        + (Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β) := by
    ring
  calc ‖Work.FITop4.Tbeta (Work.FITop.radN Pa) β‖
      = ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X β + Work.FITop4.Vcut (Work.FITop.radN Pa) X β
          + Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖ := by
          rw [hT]
    _ = ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X β + Work.FITop4.Vcut (Work.FITop.radN Pa) X β
          + (Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β)‖ := by
          rw [hgrp]
    _ ≤ ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X β + Work.FITop4.Vcut (Work.FITop.radN Pa) X β‖
          + ‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖ :=
          norm_add_le _ _
    _ ≤ (‖Work.FITop4.Ucut (Work.FITop.radN Pa) X β‖ + ‖Work.FITop4.Vcut (Work.FITop.radN Pa) X β‖)
          + ‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖ :=
          add_le_add_left (norm_add_le _ _) _
    _ = ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X β‖ + ‖Work.FITop4.Vcut (Work.FITop.radN Pa) X β‖
          + ‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖ := rfl
    _ ≤ cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
          + cE * Pa.N ^ 2 * (Real.log Pa.N) ^ (-σ)
          + cV * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ) ^ (-(1 : ℝ) / 3)) * Pa.N ^ 2
          + cW * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
          have h := add_le_add (add_le_add hU hV) hW
          linarith
    _ ≤ (cU + cV + cW + cE) * (Pa.N ^ 2 * (Real.log Pa.N) ^ (-σ)
          + (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N) := by
          have hE' : cE * Pa.N ^ 2 * (Real.log Pa.N) ^ (-σ)
              ≤ cE * (Pa.N ^ 2 * (Real.log Pa.N) ^ (-σ)
                  + (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N) := by
            have h2 : 0 ≤ Pa.N ^ 2 * (Real.log Pa.N) ^ (-σ) := by positivity
            have h3 : 0 ≤ (Pa.Pz : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N := by positivity
            nlinarith [hcE, h2, h3]
          linarith [hU', hV', hW', hE']

end Work.FIRed6e
