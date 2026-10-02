import Mathlib
import Submission.Work.Implosion.Approx.modelDisp_bounds
import Submission.Work.Implosion.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

open Complex

theorem norm_modelDisp_add_rational_le (lam : ℝ) (hlam : 0 < lam) (hlam8 : lam ≤ 1 / 8)
    (h : ℂ → ℂ) (u : ℂ)
    (hζ : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 1 / 4)
    (hH : ‖h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u)‖ ≤ 2) :
    ‖Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u
      + h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u)
        / (1 + Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u
            * h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u))‖
      ≤ 100 * lam ^ 2 := by
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set ζ : ℂ := Work.Implosion.ecalPt a u with hζa
  set H : ℂ := h ζ with hHa
  set c : ℂ := 1 + ζ * H with hc
  set w : ℂ := a * H / c with hw
  have hlne : lam ≠ 0 := ne_of_gt hlam
  have ha0 : a ≠ 0 := by
    rw [ha]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hlne) Complex.I_ne_zero
  have hanorm : ‖a‖ = lam := by
    rw [ha, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos hlam
  have hζH : ‖ζ * H‖ ≤ 1 / 2 := by
    rw [norm_mul]
    calc ‖ζ‖ * ‖H‖ ≤ (1 / 4) * 2 :=
          mul_le_mul hζ hH (norm_nonneg H) (by norm_num)
      _ = 1 / 2 := by norm_num
  have hcd : ‖c - 1‖ ≤ 1 / 2 := by
    have hce : c - 1 = ζ * H := by rw [hc]; ring
    rw [hce]; exact hζH
  have hc_lower : (1 / 2 : ℝ) ≤ ‖c‖ := by
    have h1 : (1 : ℝ) - ‖c‖ ≤ ‖(1 : ℂ) - c‖ := by
      have := norm_sub_norm_le (1 : ℂ) c
      rwa [norm_one] at this
    rw [norm_sub_rev] at h1
    linarith
  have hre_c : 0 < c.re := by
    have h2 : c.re = 1 + (ζ * H).re := by rw [hc]; simp
    have h5 := (abs_le.mp (Complex.abs_re_le_norm (ζ * H))).1
    rw [h2]; linarith
  have hc0 : c ≠ 0 := by intro h0; rw [h0] at hre_c; simp at hre_c
  have hw_le : ‖w‖ ≤ 4 * lam := by
    have h1 : ‖w‖ = lam * (‖H‖ / ‖c‖) := by
      rw [hw, norm_div, norm_mul, hanorm, mul_div_assoc]
    rw [h1]
    have hHc : ‖H‖ / ‖c‖ ≤ 4 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖c‖)]
      nlinarith [hH, hc_lower]
    calc lam * (‖H‖ / ‖c‖) ≤ lam * 4 := mul_le_mul_of_nonneg_left hHc (le_of_lt hlam)
      _ = 4 * lam := by ring
  have hw_small : ‖w‖ ≤ 3 / 5 := by
    have h4 : 4 * lam ≤ 4 * (1 / 8 : ℝ) := by linarith
    linarith
  have hw_lt1 : ‖w‖ < 1 := lt_of_le_of_lt hw_small (by norm_num)
  have hre1w : 0 < (1 - w).re := by
    have hre : (1 - w).re = 1 - w.re := by simp
    have hle : w.re ≤ ‖w‖ := (abs_le.mp (Complex.abs_re_le_norm w)).2
    rw [hre]; linarith [hw_lt1]
  have hre1wp : 0 < (1 + w).re := by
    have hre : (1 + w).re = 1 + w.re := by simp
    have hle : -‖w‖ ≤ w.re := (abs_le.mp (Complex.abs_re_le_norm w)).1
    rw [hre]; linarith [hw_lt1]
  have hw1 : 1 - w ≠ 0 := by intro h0; rw [h0] at hre1w; simp at hre1w
  have hw2 : 1 + w ≠ 0 := by intro h0; rw [h0] at hre1wp; simp at hre1wp
  have ha1 : c.arg + (1 - w).arg ∈ Set.Ioc (-Real.pi) Real.pi :=
    Work.Implosion.Approx.arg_add_mem_Ioc_of_re_pos hre_c hre1w
  have ha2 : c.arg + (1 + w).arg ∈ Set.Ioc (-Real.pi) Real.pi :=
    Work.Implosion.Approx.arg_add_mem_Ioc_of_re_pos hre_c hre1wp
  have hid : 2 * a * (Work.Implosion.modelDisp a h u + H * c⁻¹)
      = Work.Implosion.Approx.logRem (-w) - Work.Implosion.Approx.logRem w :=
    Work.Implosion.Approx.two_a_mul_modelDisp_add_inv a h u ζ H c w ha0 hζa hHa hc hw
      hc0 hw1 hw2 ha1 ha2
  have h2a : (2 : ℂ) * a ≠ 0 := mul_ne_zero (by norm_num) ha0
  have hsplit : Work.Implosion.modelDisp a h u + H * c⁻¹
      = (Work.Implosion.Approx.logRem (-w) - Work.Implosion.Approx.logRem w) / (2 * a) := by
    rw [eq_div_iff h2a, mul_comm]
    exact hid
  have hlogRem_neg : ‖Work.Implosion.Approx.logRem (-w)‖ ≤ 5 * ‖w‖ ^ 3 / 6 := by
    have h := Work.Implosion.Approx.norm_logRem_le_three_fifths (-w)
      (by rw [norm_neg]; exact hw_small)
    simpa [norm_neg] using h
  have hlogRem_pos : ‖Work.Implosion.Approx.logRem w‖ ≤ 5 * ‖w‖ ^ 3 / 6 :=
    Work.Implosion.Approx.norm_logRem_le_three_fifths w hw_small
  have hcorr : ‖Work.Implosion.modelDisp a h u + H * c⁻¹‖ ≤ 5 * ‖w‖ ^ 3 / (6 * lam) := by
    rw [hsplit, norm_div]
    have h2an : ‖(2 : ℂ) * a‖ = 2 * lam := by
      rw [norm_mul, hanorm]; norm_num
    rw [h2an]
    have hsum : ‖Work.Implosion.Approx.logRem (-w) - Work.Implosion.Approx.logRem w‖
        ≤ 5 * ‖w‖ ^ 3 / 3 := by
      calc ‖Work.Implosion.Approx.logRem (-w) - Work.Implosion.Approx.logRem w‖
          ≤ ‖Work.Implosion.Approx.logRem (-w)‖ + ‖Work.Implosion.Approx.logRem w‖ :=
            norm_sub_le _ _
        _ ≤ 5 * ‖w‖ ^ 3 / 6 + 5 * ‖w‖ ^ 3 / 6 := add_le_add hlogRem_neg hlogRem_pos
        _ = 5 * ‖w‖ ^ 3 / 3 := by ring
    calc ‖Work.Implosion.Approx.logRem (-w) - Work.Implosion.Approx.logRem w‖ / (2 * lam)
        ≤ (5 * ‖w‖ ^ 3 / 3) / (2 * lam) :=
          div_le_div_of_nonneg_right hsum (by linarith)
      _ = 5 * ‖w‖ ^ 3 / (6 * lam) := by ring
  have hfin : 5 * ‖w‖ ^ 3 / (6 * lam) ≤ 100 * lam ^ 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 6 * lam)]
    have hw3 : ‖w‖ ^ 3 ≤ (4 * lam) ^ 3 := pow_le_pow_left₀ (norm_nonneg w) hw_le 3
    nlinarith [hw3, hlam]
  simpa [div_eq_mul_inv] using le_trans hcorr hfin

end Work.PARIMPL2.Direct
