/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Mathlib
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.rep_norm_transfer
import Submission.Work.PARIMPL2.Lavaurs.RepNorm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.rep_norm_transfer_stolz`

The Stolz-sector form of the repelling normalisation transfer `Work.FlowerGlue2.rep_norm_transfer`:
the inverse-germ hypothesis `hVinv` is only required on the *Stolz sector* `|Im w| < -Re w + 1`
(rather than on the whole half-plane `Re w < -R₀`), and the flower's repelling coordinate is
replaced by an abstract `Ψ` in transfer form.  The conclusion is the area-`PARIMPL2` bundle
`Work.PARIMPL2.Lavaurs.RepNorm`.

The proof is the same estimate as in `rep_norm_transfer`; the only new ingredient is that the
points `w = w0 P z` of the outgoing geometric window lie in the Stolz sector, because
`|Im w| ≤ H ≤ R/8` while `-Re w ≥ R`, so `|Im w| < -Re w + 1` whenever `R ≥ 8(H+1)`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

open Filter Set Metric
open scoped Topology

namespace Work.FlowerGlue2

open Work.PARIMPL (ParNormal)

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- Pure real asymptotic helper: for any real `A B C` the expression
`A log (2R) + B + C (1 + log (2R))/R` is eventually below `R/2`. -/
private lemma exists_log_bound_stolz (A B C : ℝ) :
    ∃ N : ℝ, 1 ≤ N ∧ ∀ R ≥ N,
      A * Real.log (2 * R) + B + C * (1 + Real.log (2 * R)) / R < R / 2 := by
  have hlog_div : Tendsto (fun R : ℝ => Real.log R / R) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1:ℝ) ≠ 0)
    simpa using h
  have hinv : Tendsto (fun R : ℝ => (1:ℝ) / R) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero (𝕜 := ℝ)
    simpa [one_div] using h
  have hg : Tendsto (fun R : ℝ => Real.log (2 * R) / R) atTop (𝓝 0) := by
    have hlog2 : Tendsto (fun R : ℝ => Real.log 2 / R) atTop (𝓝 0) := by
      have h := hinv.const_mul (Real.log 2)
      simpa [div_eq_mul_inv, one_div, mul_comm] using h
    have hsum : Tendsto (fun R : ℝ => Real.log 2 / R + Real.log R / R) atTop (𝓝 0) := by
      have := hlog2.add hlog_div
      simpa using this
    refine hsum.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with R hR
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hR)]
    ring
  have hL : Tendsto (fun R : ℝ =>
      A * (Real.log (2 * R) / R) + B * (1 / R)
        + C * ((1 / R) * (1 / R) + (Real.log (2 * R) / R) * (1 / R)))
      atTop (𝓝 0) := by
    have ht1 : Tendsto (fun R : ℝ => A * (Real.log (2 * R) / R)) atTop (𝓝 0) := by
      have := hg.const_mul A
      simpa using this
    have ht2 : Tendsto (fun R : ℝ => B * (1 / R)) atTop (𝓝 0) := by
      have := hinv.const_mul B
      simpa using this
    have ht3 : Tendsto (fun R : ℝ =>
        (1 / R) * (1 / R) + (Real.log (2 * R) / R) * (1 / R)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => (1 / R) * (1 / R)) atTop (𝓝 0) := by
        have := hinv.mul hinv
        simpa using this
      have h2 : Tendsto (fun R : ℝ => (Real.log (2 * R) / R) * (1 / R)) atTop (𝓝 0) := by
        have := hg.mul hinv
        simpa using this
      have := h1.add h2
      simpa using this
    have := (ht1.add ht2).add (ht3.const_mul C)
    simpa using this
  have hev : ∀ᶠ R in atTop,
      (A * Real.log (2 * R) + B + C * (1 + Real.log (2 * R)) / R) / R < 1 / 2 := by
    have h := hL.eventually (Iio_mem_nhds (show (0:ℝ) < 1/2 by norm_num))
    filter_upwards [h, Filter.eventually_gt_atTop (0:ℝ)] with R hR hRpos
    have hReq : (A * Real.log (2 * R) + B + C * (1 + Real.log (2 * R)) / R) / R
        = A * (Real.log (2 * R) / R) + B * (1 / R)
            + C * ((1 / R) * (1 / R) + (Real.log (2 * R) / R) * (1 / R)) := by
      have hRne : R ≠ 0 := ne_of_gt hRpos
      field_simp
      try ring
    rw [hReq]
    exact hR
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max N₀ 1, le_max_right _ _, ?_⟩
  intro R hR
  have hR0 : N₀ ≤ R := le_trans (le_max_left _ _) hR
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hlt := hN₀ R hR0
  have h := (div_lt_iff₀ hRpos).mp hlt
  linarith

/-- Elementary bounds of the `c₀`-chart coordinate on the outgoing geometric window:
on `WoutG P R H` (with `H ≥ 0`) one has `R ≤ ‖w0 P z‖ ≤ R + H + 2`. -/
private lemma w0_bounds_stolz {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} {P : Work.PARIMPL.ParNormal d}
    {R H : ℝ} (hR : 0 < R) (hH : 0 ≤ H) {z : ℂ} (hz : z ∈ WoutG P R H) :
    R ≤ ‖w0 P z‖ ∧ ‖w0 P z‖ ≤ R + H + 2 := by
  obtain ⟨hz1, hre, him⟩ := hz
  obtain ⟨hre1, hre2⟩ := hre
  have habs : |(w0 P z).re| ≤ R + 2 := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_⟩
  · calc R ≤ -(w0 P z).re := by linarith
      _ ≤ |(w0 P z).re| := neg_le_abs _
      _ ≤ ‖w0 P z‖ := Complex.abs_re_le_norm _
  · have hsq : ‖w0 P z‖ ^ 2 ≤ (R + H + 2) ^ 2 := by
      have h1 : (w0 P z).re ^ 2 ≤ (R + 2) ^ 2 := by
        have hb := abs_le.mp habs
        nlinarith [hb.1, hb.2, hR]
      have h2 : (w0 P z).im ^ 2 ≤ H ^ 2 := by
        have hb := abs_le.mp him
        nlinarith [hb.1, hb.2, hH]
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [hre2, h1, h2, hR, hH]
    nlinarith [hsq, norm_nonneg (w0 P z), hre2, him, abs_nonneg (w0 P z).im, hR, hH]

/-- Bound on the real part of `w0 P z - (1 - h₁) Λ (w0 P z)` (the argument of the repelling
inverse) on the outgoing window: it is at most `-R + O(log R)`. -/
private lemma re_X_bound_stolz {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (hτ : P.h c₀ 0 = 1) {R H : ℝ} (hR : 0 < R) (hR1 : 1 ≤ R) (hH : 0 ≤ H) {z : ℂ}
    (hz : z ∈ WoutG P R H) (h2R : ‖w0 P z‖ ≤ 2 * R) :
    (w0 P z - (1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z)).re
      ≤ -R + ‖P.κ c₀‖ * Real.log (2 * R) + 2 * Real.pi * ‖P.κ c₀‖ := by
  have hmem : c₀ ∈ ball c₀ P.ρ₀ := mem_ball_self P.hρ₀
  have hκ : P.κ c₀ = 1 - P.h1 c₀ := by
    have h := (P.κ_eq c₀ hmem).2
    rw [hτ] at h
    simpa using h
  have hwre : (w0 P z).re ≤ -R := hz.2.1.2
  have hwpos : 0 < ‖w0 P z‖ := by
    have h := (w0_bounds_stolz hR hH hz).1
    linarith
  have hstep : (w0 P z - (1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z)).re
      ≤ (w0 P z).re + ‖(1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z)‖ := by
    have h1 := Complex.abs_re_le_norm ((1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z))
    have h1' := neg_le_abs (((1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z)).re)
    have h2 : (w0 P z - (1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z)).re
        = (w0 P z).re - ((1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z)).re :=
      Complex.sub_re _ _
    rw [h2]
    linarith
  have hLam : ‖Work.FatouCoord.Petal.Lambda (w0 P z)‖ ≤ Real.log (2 * R) + 2 * Real.pi := by
    rw [Work.FatouCoord.Petal.Lambda_apply]
    have h1 : ‖Complex.log (-(w0 P z)) + (Real.pi : ℂ) * Complex.I‖
        ≤ ‖Complex.log (-(w0 P z))‖ + ‖(Real.pi : ℂ) * Complex.I‖ := norm_add_le _ _
    have h2 : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
      exact abs_of_nonneg Real.pi_pos.le
    have h3 : ‖Complex.log (-(w0 P z))‖ ≤ Real.log (2 * R) + Real.pi := by
      have hb := Complex.norm_le_abs_re_add_abs_im (Complex.log (-(w0 P z)))
      have hre : (Complex.log (-(w0 P z))).re = Real.log ‖w0 P z‖ := by
        rw [Complex.log_re, norm_neg]
      have him : (Complex.log (-(w0 P z))).im = (-(w0 P z)).arg := Complex.log_im _
      rw [hre, him] at hb
      have harg : |(-(w0 P z)).arg| ≤ Real.pi := Complex.abs_arg_le_pi _
      have hlw : Real.log ‖w0 P z‖ ≤ Real.log (2 * R) := Real.log_le_log hwpos h2R
      have hpos : 0 ≤ Real.log ‖w0 P z‖ := Real.log_nonneg (by
        have h := (w0_bounds_stolz hR hH hz).1
        linarith)
      rw [abs_of_nonneg hpos] at hb
      linarith
    linarith
  have hnorm : ‖(1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z)‖
      ≤ ‖P.κ c₀‖ * (Real.log (2 * R) + 2 * Real.pi) := by
    have hmul : ‖(1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z)‖
        = ‖1 - P.h1 c₀‖ * ‖Work.FatouCoord.Petal.Lambda (w0 P z)‖ := norm_mul _ _
    have heq : ‖1 - P.h1 c₀‖ = ‖P.κ c₀‖ := by rw [hκ]
    rw [hmul, heq]
    exact mul_le_mul_of_nonneg_left hLam (norm_nonneg _)
  linarith [hstep, hnorm, hwre]

theorem rep_norm_transfer_stolz {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) (hτ : P.h c₀ 0 = 1) (sh : ℂ)
    {V Ψ : ℂ → ℂ} {R₀ K₀ : ℝ} (hR₀ : 0 < R₀) (hK₀ : 0 < K₀)
    (hVinv : ∀ w : ℂ, w.re < -R₀ → |w.im| < -w.re + 1 → ∃ v : ℂ, v.re < -R₀ ∧ V v = w ∧
      ‖v - (w - (1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda w)‖
        ≤ K₀ * (1 + Real.log ‖w‖) / ‖w‖)
    (hΨ : ∀ w : ℂ, Ψ w = d.z₁ + P.s c₀ * (-1 / V (w + sh))) :
    Work.PARIMPL2.Lavaurs.RepNorm P Ψ := by
  have hs : P.s c₀ ≠ 0 := P.s_ne c₀ (mem_ball_self P.hρ₀)
  have hκ : P.κ c₀ = 1 - P.h1 c₀ := by
    have h := (P.κ_eq c₀ (mem_ball_self P.hρ₀)).2
    rw [hτ] at h
    simpa using h
  obtain ⟨N₁, hN₁a, hN₁⟩ :=
    exists_log_bound_stolz ‖P.κ c₀‖ (2 * Real.pi * ‖P.κ c₀‖ - sh.re) K₀
  show ∃ sr : ℂ, ∃ N K : ℝ, 0 < N ∧ 0 ≤ K ∧
      ∀ R ≥ N, ∀ H : ℝ, R ≥ 8 * (H + 1) → ∀ z ∈ WoutG P R H,
        ∃ u : ℂ, u.re < -(R / 2) ∧ Ψ u = z ∧
          ‖u - (approxCoordRep (P.κ c₀) (w0 P z) + sr)‖
            ≤ K * (1 + H) * (1 + Real.log R) / R
  refine ⟨-sh - (1 - P.h1 c₀) * ((Real.pi : ℂ) * Complex.I),
    max (max (R₀ + 1) (16 / 7)) N₁, K₀ * (1 + Real.log 2), ?_, ?_, ?_⟩
  · have h1 : (16:ℝ)/7 ≤ max (max (R₀ + 1) (16/7)) N₁ :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  · have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [hK₀.le, h2]
  · intro R hR H hRH z hz
    have hR₁ : N₁ ≤ R := le_trans (le_max_right _ _) hR
    have hRbig : R₀ + 1 ≤ R := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hR)
    have hR167 : (16:ℝ)/7 ≤ R := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hR)
    have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR167
    have hHnn : 0 ≤ H := le_trans (abs_nonneg _) hz.2.2
    have hHle : H ≤ R / 8 := by linarith
    have hwre : (w0 P z).re ≤ -R := hz.2.1.2
    have hwlt : (w0 P z).re < -R₀ := by linarith
    have hwstolz : |(w0 P z).im| < -(w0 P z).re + 1 := by
      have h1 : |(w0 P z).im| ≤ H := hz.2.2
      have h2 : R / 8 < R + 1 := by linarith
      linarith
    obtain ⟨v, hv1, hv2, hv3⟩ := hVinv (w0 P z) hwlt hwstolz
    have hwb := w0_bounds_stolz hRpos hHnn hz
    have hRnorm : R ≤ ‖w0 P z‖ := hwb.1
    have hnormupper : ‖w0 P z‖ ≤ R + H + 2 := hwb.2
    have h2R : ‖w0 P z‖ ≤ 2 * R := by linarith
    have hnormpos : 0 < ‖w0 P z‖ := lt_of_lt_of_le hRpos hRnorm
    have hvX : v.re ≤ (w0 P z - (1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z)).re
        + K₀ * (1 + Real.log ‖w0 P z‖) / ‖w0 P z‖ := by
      have h1 := Complex.re_le_norm
        (v - (w0 P z - (1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z)))
      rw [Complex.sub_re] at h1
      linarith [hv3]
    have hRone : 1 ≤ R := by linarith
    have hXre := re_X_bound_stolz P hτ hRpos hRone hHnn hz h2R
    have hnormterm : K₀ * (1 + Real.log ‖w0 P z‖) / ‖w0 P z‖
        ≤ K₀ * (1 + Real.log (2 * R)) / R := by
      have hlog_le : Real.log ‖w0 P z‖ ≤ Real.log (2 * R) := Real.log_le_log hnormpos h2R
      have hlog_nn : 0 ≤ Real.log ‖w0 P z‖ := Real.log_nonneg (by linarith)
      have hnum_nn : 0 ≤ 1 + Real.log ‖w0 P z‖ := by linarith
      have hnum_le : 1 + Real.log ‖w0 P z‖ ≤ 1 + Real.log (2 * R) := by linarith
      have hcnn : 0 ≤ 1 + Real.log (2 * R) := by
        have := Real.log_nonneg (show (1:ℝ) ≤ 2 * R by linarith)
        linarith
      have hdiv : (1 + Real.log ‖w0 P z‖) / ‖w0 P z‖ ≤ (1 + Real.log (2 * R)) / R :=
        div_le_div₀ hcnn hnum_le hRpos hRnorm
      calc K₀ * (1 + Real.log ‖w0 P z‖) / ‖w0 P z‖
          = K₀ * ((1 + Real.log ‖w0 P z‖) / ‖w0 P z‖) := by ring
        _ ≤ K₀ * ((1 + Real.log (2 * R)) / R) := mul_le_mul_of_nonneg_left hdiv hK₀.le
        _ = K₀ * (1 + Real.log (2 * R)) / R := by ring
    have hlogb := hN₁ R hR₁
    have hReu : (v - sh).re < -(R / 2) := by
      have hvsh : (v - sh).re = v.re - sh.re := Complex.sub_re v sh
      have h1 : v.re ≤ -R + ‖P.κ c₀‖ * Real.log (2 * R) + 2 * Real.pi * ‖P.κ c₀‖
          + K₀ * (1 + Real.log (2 * R)) / R := by linarith
      rw [hvsh]
      linarith
    refine ⟨v - sh, hReu, ?_, ?_⟩
    · rw [hΨ (v - sh)]
      have h1 : v - sh + sh = v := by ring
      rw [h1, hv2]
      have hzd : z - d.z₁ ≠ 0 := sub_ne_zero.mpr hz.1
      rw [w0_apply]
      field_simp
      ring
    · have hkey : (v - sh) - (approxCoordRep (P.κ c₀) (w0 P z)
            + (-sh - (1 - P.h1 c₀) * ((Real.pi : ℂ) * Complex.I)))
          = v - (w0 P z - (1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z)) := by
        rw [approxCoordRep_apply, Work.FatouCoord.Petal.Lambda_apply, hκ]
        ring
      rw [hkey]
      calc ‖v - (w0 P z - (1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z))‖
          ≤ K₀ * (1 + Real.log ‖w0 P z‖) / ‖w0 P z‖ := hv3
        _ ≤ K₀ * (1 + Real.log (2 * R)) / R := hnormterm
        _ ≤ K₀ * (1 + Real.log 2) * (1 + H) * (1 + Real.log R) / R := by
            have hR1 : 1 ≤ R := by linarith
            have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg hR1
            have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
            have hsplit : Real.log (2 * R) = Real.log 2 + Real.log R :=
              Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hRpos)
            have hnum1 : 1 + Real.log (2 * R) ≤ (1 + Real.log 2) * (1 + Real.log R) := by
              rw [hsplit]
              nlinarith [hlog2_nn, hlogR_nn, mul_nonneg hlog2_nn hlogR_nn]
            have hnum2 : (1 + Real.log 2) * (1 + Real.log R)
                ≤ (1 + Real.log 2) * (1 + H) * (1 + Real.log R) := by
              nlinarith [hlog2_nn, hlogR_nn, hHnn]
            have hA : K₀ * (1 + Real.log (2 * R)) / R
                ≤ K₀ * ((1 + Real.log 2) * (1 + Real.log R)) / R :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum1 hK₀.le) hRpos.le
            have hB : K₀ * ((1 + Real.log 2) * (1 + Real.log R)) / R
                ≤ K₀ * ((1 + Real.log 2) * (1 + H) * (1 + Real.log R)) / R :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum2 hK₀.le) hRpos.le
            simpa only [mul_assoc] using le_trans hA hB

end

end Work.FlowerGlue2
