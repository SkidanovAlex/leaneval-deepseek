/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.LavaursA.exit_zeta_lo` — the chart coordinate is bounded below on the exit window

The outgoing end of the transit sits in the chart at `ζ ≈ 1/R`: the approximate coordinate
`approxU P c z = approxEcal (a c) (κ c) (ecalCoord (a c) ζ)` is asymptotic to `1/ζ` there, so
the level condition `Re (approxU P c z) ∈ [R, R+2]` with `|Im (approxU P c z)| ≤ H` and
`‖ζ‖ ≤ 4/R` forces `‖ζ‖ ≥ 1/(4R)` — this is the first conjunct of the outgoing level
`Work.PARIMPL2.LavaursA.wout_level`, and the hypothesis that makes the outgoing window
non-degenerate for the MATCH comparison.

The proof is a two-regime comparison of `approxEcal (a c) (κ c) (ecalCoord (a c) ζ)` with `1/ζ`:

* **regime `4‖a‖ ≤ ‖ζ‖`** (`approxEcal_sub_inv_le`): `ecalCoord a ζ = 1/ζ + O(‖a‖²/‖ζ‖³)` with
  no lower bound on `‖ζ‖` (`Work.PARIMPL2.ecalCoord_sub_inv_le_small`), and the correction
  `κ log (sinh (a·u)/a)` is of size `‖κ‖(log (1/‖ζ‖) + 6)`; then the level condition
  `Re Ũ ∈ [R, R+2]`, `|Im Ũ| ≤ H`, `R ≥ 8(H+1)` forces `‖ζ‖ ≥ 1/(4R)` (`zeta_level_core`) by an
  elementary real-variable argument (`T = 1/‖ζ‖` satisfies `T ≤ D + c log T`, hence
  `T ≤ 4c² + 2D`, against `T > 4R`).
* **regime `‖ζ‖ < 4‖a‖`** (`approxEcal_norm_ge_small_zeta`): `mobius a ζ` is then at distance
  `≥ 2/5` from `1`, so `‖ecalCoord a ζ‖ ≥ 1/(10‖a‖)`, and the correction is only
  `O(log(1/‖a‖))`; hence `‖approxU‖ ≥ 1/(20‖a‖) - ‖κ‖(log(1/‖a‖) + π) > 2R` for `‖a‖` small,
  contradicting `‖approxU‖ ≤ R + 2 + H ≤ 2R`.
-/
import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.approxEcal_end_out_small

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.LavaursA

open Complex

/-! ## §1 Two elementary estimates for `sinh` -/

/-- `sinh w = w + O(‖w‖²)` on `‖w‖ ≤ 1`, with the constant `1`: from
`‖exp ±w − 1 ∓ w‖ ≤ ‖w‖²` (`Complex.norm_exp_sub_one_sub_id_le`). -/
theorem norm_sinh_sub_self_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖Complex.sinh w - w‖ ≤ ‖w‖ ^ 2 := by
  have h1 : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hw
  have h2 : ‖Complex.exp (-w) - 1 - (-w)‖ ≤ ‖w‖ ^ 2 := by
    have h := Complex.norm_exp_sub_one_sub_id_le (x := -w) (by rwa [norm_neg])
    rwa [norm_neg] at h
  have hdecomp : Complex.sinh w - w
      = ((Complex.exp w - 1 - w) - (Complex.exp (-w) - 1 - (-w))) / 2 := by
    rw [Complex.sinh]; ring
  have htri : ‖(Complex.exp w - 1 - w) - (Complex.exp (-w) - 1 - (-w))‖ ≤ 2 * ‖w‖ ^ 2 := by
    calc ‖(Complex.exp w - 1 - w) - (Complex.exp (-w) - 1 - (-w))‖
        ≤ ‖Complex.exp w - 1 - w‖ + ‖Complex.exp (-w) - 1 - (-w)‖ := norm_sub_le _ _
      _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := add_le_add h1 h2
      _ = 2 * ‖w‖ ^ 2 := by ring
  rw [hdecomp, norm_div, Complex.norm_ofNat]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- `‖w‖/2 ≤ ‖sinh w‖` on `‖w‖ ≤ 1/2`. -/
theorem half_norm_le_norm_sinh {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : ‖w‖ / 2 ≤ ‖Complex.sinh w‖ := by
  have hw1 : ‖w‖ ≤ 1 := by linarith
  have h : ‖Complex.sinh w - w‖ ≤ ‖w‖ ^ 2 := norm_sinh_sub_self_le hw1
  have h2 : ‖w‖ ≤ ‖Complex.sinh w - w‖ + ‖Complex.sinh w‖ := by
    have heq : Complex.sinh w - (Complex.sinh w - w) = w := by ring
    calc ‖w‖ = ‖Complex.sinh w - (Complex.sinh w - w)‖ := by rw [heq]
      _ ≤ ‖Complex.sinh w‖ + ‖Complex.sinh w - w‖ := norm_sub_le _ _
      _ = ‖Complex.sinh w - w‖ + ‖Complex.sinh w‖ := by ring
  nlinarith [norm_nonneg w, norm_nonneg (Complex.sinh w)]

/-! ## §2 The sharp small-`ζ` form of the outgoing asymptotics -/

/-- **The outgoing coordinate is `1/ζ` up to a small relative error.**  For `a ≠ 0`, `Re ζ > 0`,
`‖ζ‖ ≤ 1` and `4‖a‖ ≤ ‖ζ‖` one has

  `‖approxEcal a κ (ecalCoord a ζ) − 1/ζ‖ ≤ 1/(36‖ζ‖) + ‖κ‖(log (1/‖ζ‖) + 6)`.

The point is the *relative* smallness of the error: `ecalCoord a ζ = 1/ζ + O(‖a‖²/‖ζ‖³)` is
`O(1/(36‖ζ‖))`, and the logarithmic correction `κ·log (sinh (a u)/a)` differs from `−κ log ζ` by a
*bounded* amount: `sinh (a u)/a · ζ ≈ 1` because `u ≈ 1/ζ` and `sinh z/z ≈ 1`.  (The naive
`‖log (sinh (au)/a)‖ ≤ log(1/‖a‖) + O(1)` would give `log(1/‖ζ‖) + log 4`, which is what is
used.) -/
theorem approxEcal_sub_inv_le {a κ ζ : ℂ} (ha : a ≠ 0) (hre : 0 < ζ.re) (hζ1 : ‖ζ‖ ≤ 1)
    (haζ : 4 * ‖a‖ ≤ ‖ζ‖) :
    ‖Work.Implosion.approxEcal a κ (Work.Implosion.ecalCoord a ζ) - 1 / ζ‖
      ≤ 1 / (36 * ‖ζ‖) + ‖κ‖ * (Real.log (1 / ‖ζ‖) + 6) := by
  have ht : 0 < ‖ζ‖ := lt_of_lt_of_le hre (Complex.re_le_norm ζ)
  have htne : ζ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ht)
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have ht1 : 1 ≤ 1 / ‖ζ‖ := by rw [le_div_iff₀ ht]; linarith
  have hlognonneg : 0 ≤ Real.log (1 / ‖ζ‖) := Real.log_nonneg ht1
  set u : ℂ := Work.Implosion.ecalCoord a ζ with hu
  have hinv : ‖(1 : ℂ) / ζ‖ = 1 / ‖ζ‖ := by rw [norm_div, norm_one]
  have hu_sub : ‖u - 1 / ζ‖ ≤ 1 / (36 * ‖ζ‖) := by
    have h := Work.PARIMPL2.ecalCoord_sub_inv_le_small a ζ ha htne haζ
    rw [hu]
    have ha2 : ‖a‖ ^ 2 ≤ ‖ζ‖ ^ 2 / 16 := by nlinarith [haζ, norm_nonneg a, norm_nonneg ζ]
    have hkey : 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 ≤ 1 / (36 * ‖ζ‖) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [ha2, ht]
    linarith
  have hu_low_c : 35 / 36 ≤ ‖u‖ * ‖ζ‖ := by
    have h1 : ‖(1 : ℂ) / ζ‖ ≤ ‖u‖ + ‖u - 1 / ζ‖ := by
      calc ‖(1 : ℂ) / ζ‖ = ‖u - (u - 1 / ζ)‖ := by ring_nf
        _ ≤ ‖u‖ + ‖u - 1 / ζ‖ := norm_sub_le _ _
    rw [hinv] at h1
    have h2 : (1 / ‖ζ‖) * ‖ζ‖ = 1 := by field_simp
    have h4 : (‖u - 1 / ζ‖) * ‖ζ‖ ≤ (1 / (36 * ‖ζ‖)) * ‖ζ‖ :=
      mul_le_mul_of_nonneg_right hu_sub ht.le
    have h5 : (1 / (36 * ‖ζ‖)) * ‖ζ‖ = 1 / 36 := by field_simp
    have h6 : (‖u‖ + ‖u - 1 / ζ‖) * ‖ζ‖ = ‖u‖ * ‖ζ‖ + (‖u - 1 / ζ‖) * ‖ζ‖ := by ring
    nlinarith [h1, h2, h4, h5, h6, ht]
  have hu_le_c : ‖u‖ * ‖ζ‖ ≤ 37 / 36 := by
    have h1 : ‖u‖ ≤ ‖u - 1 / ζ‖ + ‖(1 : ℂ) / ζ‖ := by
      calc ‖u‖ = ‖(u - 1 / ζ) + 1 / ζ‖ := by ring_nf
        _ ≤ ‖u - 1 / ζ‖ + ‖(1 : ℂ) / ζ‖ := norm_add_le _ _
    rw [hinv] at h1
    have h2 : (1 / ‖ζ‖) * ‖ζ‖ = 1 := by field_simp
    have h4 : ‖u - 1 / ζ‖ * ‖ζ‖ ≤ (1 / (36 * ‖ζ‖)) * ‖ζ‖ :=
      mul_le_mul_of_nonneg_right hu_sub ht.le
    have h5 : (1 / (36 * ‖ζ‖)) * ‖ζ‖ = 1 / 36 := by field_simp
    have h6 : (‖u - 1 / ζ‖ + 1 / ‖ζ‖) * ‖ζ‖
        = ‖u - 1 / ζ‖ * ‖ζ‖ + (1 / ‖ζ‖) * ‖ζ‖ := by ring
    nlinarith [h1, h2, h4, h5, h6, ht]
  have h4a : ‖a‖ ≤ ‖ζ‖ / 4 := by linarith
  have hau_le : ‖a * u‖ ≤ 37 / 144 := by
    rw [norm_mul]
    have hkey : ‖a‖ * ‖u‖ * ‖ζ‖ ≤ 37 / 144 * ‖ζ‖ := by
      calc ‖a‖ * ‖u‖ * ‖ζ‖ = ‖a‖ * (‖u‖ * ‖ζ‖) := by ring
        _ ≤ ‖a‖ * (37 / 36) := mul_le_mul_of_nonneg_left hu_le_c (norm_nonneg _)
        _ ≤ (‖ζ‖ / 4) * (37 / 36) := mul_le_mul_of_nonneg_right h4a (by norm_num)
        _ = 37 / 144 * ‖ζ‖ := by ring
    exact le_of_mul_le_mul_right hkey ht
  have hau_half : ‖a * u‖ ≤ 1 / 2 := by linarith
  have hylow_c : 35 / 72 ≤ ‖Complex.sinh (a * u) / a‖ * ‖ζ‖ := by
    have h1 : ‖a * u‖ / 2 ≤ ‖Complex.sinh (a * u)‖ := half_norm_le_norm_sinh hau_half
    have h2 : ‖a * u‖ / 2 * ‖ζ‖ ≤ ‖Complex.sinh (a * u)‖ * ‖ζ‖ :=
      mul_le_mul_of_nonneg_right h1 ht.le
    have h3 : ‖a * u‖ / 2 * ‖ζ‖ = ‖a‖ * (‖u‖ * ‖ζ‖) / 2 := by rw [norm_mul]; ring
    have h7 : ‖a‖ * (35 / 72) ≤ ‖a‖ * (‖u‖ * ‖ζ‖) / 2 := by
      have h8 := mul_le_mul_of_nonneg_left hu_low_c (norm_nonneg a)
      have h9 : ‖a‖ * (35 / 36) / 2 = ‖a‖ * (35 / 72) := by ring
      linarith [h8]
    rw [norm_div]
    rw [show ‖Complex.sinh (a * u)‖ / ‖a‖ * ‖ζ‖ = ‖Complex.sinh (a * u)‖ * ‖ζ‖ / ‖a‖ by ring]
    rw [le_div_iff₀ hna]
    calc 35 / 72 * ‖a‖ = ‖a‖ * (35 / 72) := by ring
      _ ≤ ‖a‖ * (‖u‖ * ‖ζ‖) / 2 := h7
      _ = ‖a * u‖ / 2 * ‖ζ‖ := h3.symm
      _ ≤ ‖Complex.sinh (a * u)‖ * ‖ζ‖ := h2
  have hyup_c : ‖Complex.sinh (a * u) / a‖ * ‖ζ‖ ≤ 2 := by
    have h1 : ‖Complex.sinh (a * u)‖ ≤ ‖a * u‖ + ‖a * u‖ ^ 2 := by
      have h2 : ‖Complex.sinh (a * u) - (a * u)‖ ≤ ‖a * u‖ ^ 2 :=
        norm_sinh_sub_self_le (by linarith)
      have h3 : ‖Complex.sinh (a * u)‖ ≤ ‖Complex.sinh (a * u) - (a * u)‖ + ‖a * u‖ := by
        calc ‖Complex.sinh (a * u)‖ = ‖(Complex.sinh (a * u) - a * u) + a * u‖ := by ring_nf
          _ ≤ ‖Complex.sinh (a * u) - (a * u)‖ + ‖a * u‖ := norm_add_le _ _
      linarith
    have hA : ‖a * u‖ * ‖ζ‖ ≤ ‖a‖ * (37 / 36) := by
      rw [norm_mul]
      calc ‖a‖ * ‖u‖ * ‖ζ‖ = ‖a‖ * (‖u‖ * ‖ζ‖) := by ring
        _ ≤ ‖a‖ * (37 / 36) := mul_le_mul_of_nonneg_left hu_le_c (norm_nonneg _)
    have hB : ‖a * u‖ ^ 2 * ‖ζ‖ ≤ (37 / 144) * (‖a‖ * (37 / 36)) := by
      have hp : 0 ≤ ‖a * u‖ := norm_nonneg _
      calc ‖a * u‖ ^ 2 * ‖ζ‖ = ‖a * u‖ * (‖a * u‖ * ‖ζ‖) := by ring
        _ ≤ ‖a * u‖ * (‖a‖ * (37 / 36)) := mul_le_mul_of_nonneg_left hA hp
        _ ≤ (37 / 144) * (‖a‖ * (37 / 36)) := mul_le_mul_of_nonneg_right hau_le (by positivity)
    rw [norm_div]
    rw [show ‖Complex.sinh (a * u)‖ / ‖a‖ * ‖ζ‖ = ‖Complex.sinh (a * u)‖ * ‖ζ‖ / ‖a‖ by ring]
    rw [div_le_iff₀ hna]
    calc ‖Complex.sinh (a * u)‖ * ‖ζ‖ ≤ (‖a * u‖ + ‖a * u‖ ^ 2) * ‖ζ‖ :=
          mul_le_mul_of_nonneg_right h1 ht.le
      _ = ‖a * u‖ * ‖ζ‖ + ‖a * u‖ ^ 2 * ‖ζ‖ := by ring
      _ ≤ ‖a‖ * (37 / 36) + (37 / 144) * (‖a‖ * (37 / 36)) := add_le_add hA hB
      _ = ‖a‖ * ((37 / 36) * (1 + 37 / 144)) := by ring
      _ ≤ ‖a‖ * 2 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg a)
          norm_num
      _ = 2 * ‖a‖ := by ring
  have hlogy : ‖Complex.log (Complex.sinh (a * u) / a)‖ ≤ Real.log (1 / ‖ζ‖) + 6 := by
    have hylow' : (35 : ℝ) / 72 / ‖ζ‖ ≤ ‖Complex.sinh (a * u) / a‖ := by
      rw [div_le_iff₀ ht]; exact hylow_c
    have hyup' : ‖Complex.sinh (a * u) / a‖ ≤ 2 / ‖ζ‖ := by
      rw [le_div_iff₀ ht]; exact hyup_c
    have hyne : Complex.sinh (a * u) / a ≠ 0 := by
      intro h
      have h1 : ‖Complex.sinh (a * u) / a‖ = 0 := by rw [h, norm_zero]
      have h2 : 0 < (35 : ℝ) / 72 / ‖ζ‖ := by positivity
      linarith [hylow']
    have hpos : 0 < ‖Complex.sinh (a * u) / a‖ := norm_pos_iff.mpr hyne
    have hub : |Real.log ‖Complex.sinh (a * u) / a‖| ≤ Real.log (1 / ‖ζ‖) + 2 := by
      have hup : Real.log ‖Complex.sinh (a * u) / a‖ ≤ Real.log (1 / ‖ζ‖) + 1 := by
        have h1' : Real.log ‖Complex.sinh (a * u) / a‖ ≤ Real.log (2 / ‖ζ‖) :=
          Real.log_le_log hpos hyup'
        have h2 : Real.log (2 / ‖ζ‖) = Real.log 2 + Real.log (1 / ‖ζ‖) := by
          rw [show (2 : ℝ) / ‖ζ‖ = 2 * (1 / ‖ζ‖) by ring, Real.log_mul (by norm_num) (by positivity)]
        have h3 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
        linarith
      have hlow : -(Real.log (1 / ‖ζ‖)) - 2 ≤ Real.log ‖Complex.sinh (a * u) / a‖ := by
        have h1' : Real.log ((35 : ℝ) / 72 / ‖ζ‖) ≤ Real.log ‖Complex.sinh (a * u) / a‖ :=
          Real.log_le_log (by positivity) hylow'
        have h2 : Real.log ((35 : ℝ) / 72 / ‖ζ‖) = Real.log (35 / 72) + Real.log (1 / ‖ζ‖) := by
          rw [show (35 : ℝ) / 72 / ‖ζ‖ = (35 / 72) * (1 / ‖ζ‖) by ring,
              Real.log_mul (by norm_num) (by positivity)]
        have h3 : -2 ≤ Real.log (35 / 72) := by
          have h4 : Real.log ((35 : ℝ) / 72)⁻¹ ≤ ((35 : ℝ) / 72)⁻¹ - 1 :=
            Real.log_le_sub_one_of_pos (by norm_num)
          rw [Real.log_inv] at h4
          have h5 : ((35 : ℝ) / 72)⁻¹ - 1 = 37 / 35 := by norm_num
          linarith
        linarith
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    calc ‖Complex.log (Complex.sinh (a * u) / a)‖
        ≤ |(Complex.log (Complex.sinh (a * u) / a)).re|
          + |(Complex.log (Complex.sinh (a * u) / a)).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ Real.log (1 / ‖ζ‖) + 6 := by
          rw [Complex.log_re, Complex.log_im]
          have := Complex.abs_arg_le_pi (Complex.sinh (a * u) / a)
          have hp4 := Real.pi_lt_four
          linarith
  have hdec : Work.Implosion.approxEcal a κ u - 1 / ζ
      = (u - 1 / ζ) + κ * Complex.log (Complex.sinh (a * u) / a) := by
    rw [Work.Implosion.approxEcal_apply]; ring
  rw [hdec]
  calc ‖(u - 1 / ζ) + κ * Complex.log (Complex.sinh (a * u) / a)‖
      ≤ ‖u - 1 / ζ‖ + ‖κ * Complex.log (Complex.sinh (a * u) / a)‖ := norm_add_le _ _
    _ = ‖u - 1 / ζ‖ + ‖κ‖ * ‖Complex.log (Complex.sinh (a * u) / a)‖ := by rw [norm_mul]
    _ ≤ 1 / (36 * ‖ζ‖) + ‖κ‖ * (Real.log (1 / ‖ζ‖) + 6) :=
        add_le_add hu_sub (mul_le_mul_of_nonneg_left hlogy (norm_nonneg κ))

/-! ## §3 The level condition forces `||ζ|| ≥ 1/(4R)` -/

/-- **The core estimate.**  If `u` is `1/ζ` up to `1/(36‖ζ‖) + K(log (1/‖ζ‖) + 6)`,
`Re u ∈ [R, R+2]`, `|Im u| ≤ H`, `R ≥ 8(H+1)` and `R ≥ 12K² + 22K + 8`, then `‖ζ‖ ≥ 1/(4R)`.

Write `T = 1/‖ζ‖`.  The two hypotheses give `Re (1/ζ) ≤ R + 2 + Y` and `|Im (1/ζ)| ≤ H + Y` with
`Y = T/36 + K log T + 6K`, whence `T² ≤ 2(R + 2 + Y)²`, i.e.
`T ≤ (3/2)(R + 2 + 6K) + (3/2)K log T + T/24`, or `T ≤ D + c log T` with `c = 36K/23`,
`D = (36/23)(R + 2 + 6K)`.  Since `log T ≤ 2√T` this gives `T ≤ 4c² + 2D`, and with `T > 4R` this
forces `R < [4c² + 2D - (72R/23)]/(20/23)`, contradicting `R ≥ 12K² + 22K + 8`. -/
theorem zeta_level_core {ζ u κ : ℂ} {R H K : ℝ}
    (hRH : R ≥ 8 * (H + 1)) (hK : 0 ≤ K) (hκ : ‖κ‖ ≤ K) (hre : 0 < ζ.re)
    (hdec : ‖u - 1 / ζ‖ ≤ 1 / (36 * ‖ζ‖) + K * (Real.log (1 / ‖ζ‖) + 6))
    (hur : u.re ∈ Set.Icc R (R + 2)) (huim : |u.im| ≤ H)
    (hR : R ≥ 12 * K ^ 2 + 22 * K + 8) :
    1 / (4 * R) ≤ ‖ζ‖ := by
  have hKsq : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
  have ht : 0 < ‖ζ‖ := lt_of_lt_of_le hre (Complex.re_le_norm ζ)
  have hRpos : 0 < R := by linarith
  by_contra hcon
  have hcon' : ‖ζ‖ < 1 / (4 * R) := not_le.mp hcon
  set T := 1 / ‖ζ‖ with hTdef
  have hT4R : 4 * R < T := by
    have h : 1 / (1 / (4 * R)) < T := by
      rw [hTdef]
      exact one_div_lt_one_div_of_lt ht hcon'
    rwa [one_div_one_div] at h
  have hT1 : 1 < T := by linarith
  have hTpos : 0 < T := by linarith
  have hdec' : ‖u - 1 / ζ‖ ≤ T / 36 + K * Real.log T + 6 * K := by
    have h1 : (1 : ℝ) / (36 * ‖ζ‖) = T / 36 := by rw [hTdef]; field_simp
    have h2 : K * (Real.log T + 6) = K * Real.log T + 6 * K := by ring
    linarith [hdec]
  have hYnn : 0 ≤ T / 36 + K * Real.log T + 6 * K := by
    have := Real.log_nonneg hT1.le
    nlinarith [hTpos, hK]
  -- the real and imaginary parts of `1/ζ`
  have hAre : ((1 : ℂ) / ζ).re - u.re = ((1 : ℂ) / ζ - u).re :=
    (Complex.sub_re ((1 : ℂ) / ζ) u).symm
  have hAim : ((1 : ℂ) / ζ).im - u.im = ((1 : ℂ) / ζ - u).im :=
    (Complex.sub_im ((1 : ℂ) / ζ) u).symm
  have hneg : (1 : ℂ) / ζ - u = -(u - 1 / ζ) := by ring
  have hnorm : ‖(1 : ℂ) / ζ - u‖ = ‖u - 1 / ζ‖ := by rw [hneg, norm_neg]
  have hAup : ((1 : ℂ) / ζ).re ≤ R + 2 + (T / 36 + K * Real.log T + 6 * K) := by
    have h2 : ((1 : ℂ) / ζ - u).re ≤ ‖(1 : ℂ) / ζ - u‖ :=
      (abs_le.mp (Complex.abs_re_le_norm _)).2
    have h3 : ((1 : ℂ) / ζ).re - u.re ≤ ‖u - 1 / ζ‖ := by rw [hAre, ← hnorm]; exact h2
    have h4 : u.re ≤ R + 2 := hur.2
    linarith [h3, h4, hdec']
  have hAlow : R - (T / 36 + K * Real.log T + 6 * K) ≤ ((1 : ℂ) / ζ).re := by
    have h2 : -‖(1 : ℂ) / ζ - u‖ ≤ ((1 : ℂ) / ζ - u).re :=
      (abs_le.mp (Complex.abs_re_le_norm _)).1
    have h3 : -‖u - 1 / ζ‖ ≤ ((1 : ℂ) / ζ).re - u.re := by rw [hAre, ← hnorm]; exact h2
    have h4 : R ≤ u.re := hur.1
    linarith [h3, h4, hdec']
  have hBup : |((1 : ℂ) / ζ).im| ≤ H + (T / 36 + K * Real.log T + 6 * K) := by
    have h2 : |((1 : ℂ) / ζ - u).im| ≤ ‖(1 : ℂ) / ζ - u‖ := Complex.abs_im_le_norm _
    have h3 : |u.im - ((1 : ℂ) / ζ).im| ≤ ‖u - 1 / ζ‖ := by
      rw [hnorm] at h2
      rw [← hAim, abs_sub_comm] at h2
      exact h2
    have h4 := (abs_le.mp h3)
    have h5 := (abs_le.mp huim)
    rw [abs_le]
    constructor <;> linarith [h4.1, h4.2, h5.1, h5.2, hdec']
  have hTsq : T ^ 2 = ((1 : ℂ) / ζ).re ^ 2 + ((1 : ℂ) / ζ).im ^ 2 := by
    have h1 : ‖(1 : ℂ) / ζ‖ = T := by rw [hTdef, norm_div, norm_one, one_div]
    rw [← h1, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hbound : T ^ 2 ≤ 2 * (R + 2 + (T / 36 + K * Real.log T + 6 * K)) ^ 2 := by
    have hAnn : 0 ≤ T / 36 + K * Real.log T + 6 * K := hYnn
    have hHle : H ≤ R + 2 := by linarith
    have hA2 : ((1 : ℂ) / ζ).re ^ 2 ≤ (R + 2 + (T / 36 + K * Real.log T + 6 * K)) ^ 2 := by
      refine sq_le_sq' ?_ hAup
      nlinarith [hAlow, hAnn, hRpos]
    have hB2 : ((1 : ℂ) / ζ).im ^ 2 ≤ (H + (T / 36 + K * Real.log T + 6 * K)) ^ 2 := by
      refine sq_le_sq' ?_ ((abs_le.mp hBup).2)
      linarith [(abs_le.mp hBup).1]
    have hB2' : (H + (T / 36 + K * Real.log T + 6 * K)) ^ 2
        ≤ (R + 2 + (T / 36 + K * Real.log T + 6 * K)) ^ 2 := by
      refine sq_le_sq' ?_ (by linarith)
      have h0 : 0 ≤ H + (T / 36 + K * Real.log T + 6 * K) := le_trans (abs_nonneg _) hBup
      linarith
    rw [hTsq]
    linarith
  have hTle8 : T ≤ (3 / 2) * (R + 2 + (T / 36 + K * Real.log T + 6 * K)) := by
    have hM : 0 ≤ R + 2 + (T / 36 + K * Real.log T + 6 * K) := by linarith
    have h1 : T ^ 2 ≤ ((3 / 2) * (R + 2 + (T / 36 + K * Real.log T + 6 * K))) ^ 2 := by
      nlinarith [hbound, hM]
    have h2 : |T| ≤ |(3 / 2) * (R + 2 + (T / 36 + K * Real.log T + 6 * K))| :=
      sq_le_sq.mp h1
    rw [abs_of_nonneg hTpos.le, abs_of_nonneg (by linarith)] at h2
    exact h2
  have hTle9 : T ≤ (36 / 23) * (R + 2 + 6 * K) + (36 / 23) * K * Real.log T := by
    linarith [hTle8]
  have hlogsqrt : Real.log T ≤ 2 * Real.sqrt T := by
    have h1 : Real.log (Real.sqrt T) ≤ Real.sqrt T - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hTpos)
    rw [Real.log_sqrt hTpos.le] at h1
    linarith [Real.sqrt_nonneg T]
  have hcK : 0 ≤ (36 / 23) * K := by positivity
  have hDnn : 0 ≤ (36 / 23) * (R + 2 + 6 * K) := by positivity
  have hTle10 : T ≤ (36 / 23) * (R + 2 + 6 * K) + 2 * ((36 / 23) * K) * Real.sqrt T := by
    have h4 := mul_le_mul_of_nonneg_left hlogsqrt hcK
    linarith [hTle9, h4]
  have hs2 : (Real.sqrt T) ^ 2
      ≤ (36 / 23) * (R + 2 + 6 * K) + 2 * ((36 / 23) * K) * Real.sqrt T := by
    rw [Real.sq_sqrt hTpos.le]
    exact hTle10
  have hquad : Real.sqrt T ≤ (36 / 23) * K
      + Real.sqrt (((36 / 23) * K) ^ 2 + (36 / 23) * (R + 2 + 6 * K)) := by
    have h1 : (Real.sqrt T - (36 / 23) * K) ^ 2
        ≤ ((36 / 23) * K) ^ 2 + (36 / 23) * (R + 2 + 6 * K) := by nlinarith [hs2]
    have h2 : |Real.sqrt T - (36 / 23) * K|
        ≤ Real.sqrt (((36 / 23) * K) ^ 2 + (36 / 23) * (R + 2 + 6 * K)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h1
    linarith [(abs_le.mp h2).2]
  have hTfin : T ≤ 4 * ((36 / 23) * K) ^ 2 + 2 * ((36 / 23) * (R + 2 + 6 * K)) := by
    have h1 : T = (Real.sqrt T) ^ 2 := (Real.sq_sqrt hTpos.le).symm
    have h2 : (Real.sqrt T) ^ 2
        ≤ ((36 / 23) * K + Real.sqrt (((36 / 23) * K) ^ 2 + (36 / 23) * (R + 2 + 6 * K))) ^ 2 := by
      refine sq_le_sq' ?_ hquad
      linarith [Real.sqrt_nonneg T, hcK]
    have h3 : ((36 / 23) * K + Real.sqrt (((36 / 23) * K) ^ 2 + (36 / 23) * (R + 2 + 6 * K))) ^ 2
        ≤ 4 * ((36 / 23) * K) ^ 2 + 2 * ((36 / 23) * (R + 2 + 6 * K)) := by
      have h4 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((36 / 23) * K) ^ 2 + (36 / 23) * (R + 2 + 6 * K))
      have h5 := Real.sqrt_nonneg (((36 / 23) * K) ^ 2 + (36 / 23) * (R + 2 + 6 * K))
      nlinarith [h4, h5, hcK]
    linarith
  have hcomp : 4 * ((36 / 23) * K) ^ 2 + (72 / 23) * (2 + 6 * K) ≤ (20 / 23) * (12 * K ^ 2 + 22 * K + 8) := by
    have hkey : (0 : ℝ) ≤ 336 * K ^ 2 + 184 * K + 368 := by positivity
    have hid : (20 / 23) * (12 * K ^ 2 + 22 * K + 8) - (4 * ((36 / 23) * K) ^ 2 + (72 / 23) * (2 + 6 * K))
        = (336 * K ^ 2 + 184 * K + 368) / 529 := by ring
    linarith
  have hlow : 4 * ((36 / 23) * K) ^ 2 + (72 / 23) * (2 + 6 * K) ≤ R * (20 / 23) := by
    have h1 : (20 / 23) * (12 * K ^ 2 + 22 * K + 8) ≤ (20 / 23) * R :=
      mul_le_mul_of_nonneg_left hR (by norm_num)
    linarith
  have hfinal : R * (20 / 23) < 4 * ((36 / 23) * K) ^ 2 + (72 / 23) * (2 + 6 * K) := by
    linarith [hT4R, hTfin]
  linarith

/-! ## §4 The second regime: `‖ζ‖ < 4λ` -/

/-- `e^{2z} = (e^z)²`. -/
theorem exp_two_mul (z : ℂ) : Complex.exp (2 * z) = Complex.exp z ^ 2 := by
  rw [show (2 : ℂ) * z = z + z by ring, Complex.exp_add, sq]

/-- `sinh z = (e^z − (e^z)⁻¹)/2`. -/
theorem sinh_eq_exp_sub_inv (z : ℂ) :
    Complex.sinh z = (Complex.exp z - (Complex.exp z)⁻¹) / 2 := by
  rw [Complex.sinh, Complex.exp_neg]

/-- `e^{2z} − 1 = e^z · 2 sinh z`. -/
theorem exp_two_mul_sub_one (z : ℂ) :
    Complex.exp (2 * z) - 1 = Complex.exp z * (2 * Complex.sinh z) := by
  rw [exp_two_mul, sinh_eq_exp_sub_inv]
  have h : Complex.exp z ≠ 0 := Complex.exp_ne_zero z
  field_simp

/-- **The coordinate is large when `ζ` is small.**  For `0 < λ ≤ 1`, `a = iλ`, `Re ζ > 0` and
`‖ζ‖ < 4λ` the Möbius coordinate `m = (ζ+a)/(ζ−a)` is at distance `≥ 2/5` from `1`, so
`‖log m‖ ≥ 1/5` and `‖ecalCoord a ζ‖ = ‖log m‖/(2λ) ≥ 1/(10λ)`.  Since

`‖m − 1‖ = ‖e^{a u}‖·2‖sinh (a u)‖`  and  `sinh (a·u)/a = (m−1)/(2 e^{a u} a)`
(`u = ecalCoord a ζ`), the logarithmic correction satisfies
`‖log (sinh (a u)/a)‖ ≤ log (1/λ) + ‖log m‖/2 + 9`, and the two estimates combine to
`‖approxEcal a κ (ecalCoord a ζ)‖ ≥ 1/(20λ) − ‖κ‖(log (1/λ) + 9)`. -/
theorem approxEcal_norm_ge_of_small_zeta {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    {K : ℝ} (hK : 0 ≤ K) {κ ζ : ℂ} (hκ : ‖κ‖ ≤ K) (hKlam : K ≤ 1 / (2 * lam))
    (hre : 0 < ζ.re) (ht : ‖ζ‖ < 4 * lam) :
    1 / (20 * lam) - K * (Real.log (1 / lam) + 9)
      ≤ ‖Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ
          (Work.Implosion.ecalCoord ((lam : ℂ) * Complex.I) ζ)‖ := by
  set a : ℂ := (lam : ℂ) * Complex.I with hadef
  have ha_norm : ‖a‖ = lam := by
    rw [hadef, norm_mul, Complex.norm_I, mul_one]
    simp [abs_of_pos hlam]
  have ha : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha_norm
    linarith
  have ha_re : a.re = 0 := by simp [hadef]
  have hzan : ζ ≠ a := by
    intro h
    rw [h, ha_re] at hre
    linarith
  have hzmn : ζ ≠ -a := by
    intro h
    rw [h, Complex.neg_re, ha_re] at hre
    linarith
  set m : ℂ := Work.Implosion.mobius a ζ with hmdef
  have hm_ne : m ≠ 0 := (Work.Implosion.mobius_ne_zero_iff a ζ).mpr ⟨hzmn, hzan⟩
  have hm1 : m - 1 = 2 * a / (ζ - a) := by
    rw [hmdef, Work.Implosion.mobius]
    have hza : ζ - a ≠ 0 := sub_ne_zero.mpr hzan
    field_simp
    ring
  have hdist : ‖ζ - a‖ ≤ 5 * lam := by
    calc ‖ζ - a‖ ≤ ‖ζ‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ 4 * lam + lam := by rw [ha_norm]; linarith
      _ = 5 * lam := by ring
  have hdistpos : 0 < ‖ζ - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzan)
  have hm_small : 2 / 5 ≤ ‖m - 1‖ := by
    rw [hm1, norm_div, norm_mul, ha_norm, Complex.norm_ofNat]
    rw [le_div_iff₀ hdistpos]
    nlinarith [hdist, hlam]
  have hlogm : 1 / 5 ≤ ‖Complex.log m‖ := by
    by_contra hc
    have hc' : ‖Complex.log m‖ < 1 / 5 := not_le.mp hc
    have h1 : ‖Complex.exp (Complex.log m) - 1‖ ≤ 2 * ‖Complex.log m‖ :=
      Complex.norm_exp_sub_one_le (by linarith)
    rw [Complex.exp_log hm_ne] at h1
    linarith
  have hlogm_pos : 0 ≤ ‖Complex.log m‖ := norm_nonneg _
  set u : ℂ := Work.Implosion.ecalCoord a ζ with hudef
  have hu_val : u = Complex.log m / (2 * a) := by
    rw [hudef, Work.Implosion.ecalCoord, hmdef]
  have hu_norm : ‖u‖ = ‖Complex.log m‖ / (2 * lam) := by
    rw [hu_val, norm_div, norm_mul, ha_norm, Complex.norm_ofNat]
  have haum : a * u = Complex.log m / 2 := by
    rw [hu_val]
    field_simp
  have hu_ge : 1 / (10 * lam) ≤ ‖u‖ := by
    rw [hu_norm, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hlogm, hlam]
  -- the `sinh` factor
  have hsinh_norm : ‖Complex.sinh (a * u)‖ = ‖m - 1‖ / (2 * ‖Complex.exp (a * u)‖) := by
    have h : ‖m - 1‖ = ‖Complex.exp (a * u)‖ * (2 * ‖Complex.sinh (a * u)‖) := by
      have hmw : m = Complex.exp (2 * (a * u)) := by
        rw [haum, show 2 * (Complex.log m / 2) = Complex.log m by ring]
        exact (Complex.exp_log hm_ne).symm
      rw [hmw, exp_two_mul_sub_one, norm_mul, norm_mul, Complex.norm_ofNat]
    rw [h, mul_comm]
    field_simp
  have hexp_le : ‖Complex.exp (a * u)‖ ≤ Real.exp (‖Complex.log m‖ / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h1 : (a * u).re = (Complex.log m).re / 2 := by
      have h3 : (2 * (a * u)).re = 2 * (a * u).re := by simp
      rw [show (2 : ℂ) * (a * u) = Complex.log m by rw [haum]; ring] at h3
      linarith
    rw [h1]
    have h2 : (Complex.log m).re ≤ ‖Complex.log m‖ :=
      (abs_le.mp (Complex.abs_re_le_norm (Complex.log m))).2
    linarith
  have hexp_pos : 0 < ‖Complex.exp (a * u)‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hy_ge : 1 / (5 * lam * Real.exp (‖Complex.log m‖ / 2))
      ≤ ‖Complex.sinh (a * u) / a‖ := by
    rw [norm_div, ha_norm, hsinh_norm]
    have h1 : 1 / (5 * lam * Real.exp (‖Complex.log m‖ / 2))
        ≤ 1 / (5 * lam * ‖Complex.exp (a * u)‖) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hexp_le, hlam]
    have h2 : 1 / (5 * lam * ‖Complex.exp (a * u)‖)
        ≤ ‖m - 1‖ / (2 * ‖Complex.exp (a * u)‖) / lam := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h5 : (2 / 5 : ℝ) * (5 * (lam * ‖Complex.exp (a * u)‖))
          ≤ ‖m - 1‖ * (5 * (lam * ‖Complex.exp (a * u)‖)) :=
        mul_le_mul_of_nonneg_right hm_small (by positivity)
      nlinarith [h5]
    linarith
  have hy_up : ‖Complex.sinh (a * u) / a‖ ≤ Real.exp (‖Complex.log m‖ / 2) / lam := by
    have h1 : ‖Complex.sinh (a * u)‖ ≤ Real.exp ‖a * u‖ := by
      rw [Complex.sinh, norm_div, Complex.norm_ofNat]
      calc ‖Complex.exp (a * u) - Complex.exp (-(a * u))‖ / 2
          ≤ (‖Complex.exp (a * u)‖ + ‖Complex.exp (-(a * u))‖) / 2 :=
            div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
        _ = (Real.exp (a * u).re + Real.exp (-(a * u)).re) / 2 := by
            simp only [Complex.norm_exp]
        _ ≤ Real.exp ‖a * u‖ := by
            have h2 : Real.exp (-(a * u)).re ≤ Real.exp ‖a * u‖ :=
              Real.exp_le_exp.mpr (by
                rw [Complex.neg_re]
                linarith [(abs_le.mp (Complex.abs_re_le_norm (a * u))).1])
            have h3 : Real.exp (a * u).re ≤ Real.exp ‖a * u‖ :=
              Real.exp_le_exp.mpr (Complex.re_le_norm _)
            linarith
    have h2 : ‖a * u‖ = ‖Complex.log m‖ / 2 := by rw [haum, norm_div, Complex.norm_ofNat]
    rw [norm_div, ha_norm, div_le_div_iff₀ (by positivity) hlam]
    have h3 : ‖Complex.sinh (a * u)‖ ≤ Real.exp (‖Complex.log m‖ / 2) := by
      rw [h2] at h1
      exact h1
    exact mul_le_mul_of_nonneg_right h3 hlam.le
  have hy_pos : 0 < ‖Complex.sinh (a * u) / a‖ := lt_of_lt_of_le (by positivity) hy_ge
  have hlog_up : Real.log ‖Complex.sinh (a * u) / a‖
      ≤ Real.log (1 / lam) + ‖Complex.log m‖ / 2 := by
    have h1 := Real.log_le_log hy_pos hy_up
    have h2 : Real.log (Real.exp (‖Complex.log m‖ / 2) / lam)
        = Real.log (1 / lam) + ‖Complex.log m‖ / 2 := by
      rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt hlam), Real.log_exp, one_div, Real.log_inv]
      ring
    linarith [h1, h2]
  have hlog_dn : -Real.log ‖Complex.sinh (a * u) / a‖
      ≤ Real.log 5 - Real.log (1 / lam) + ‖Complex.log m‖ / 2 := by
    have h1 := Real.log_le_log
      (by positivity : (0 : ℝ) < 1 / (5 * lam * Real.exp (‖Complex.log m‖ / 2))) hy_ge
    have h2 : Real.log (1 / (5 * lam * Real.exp (‖Complex.log m‖ / 2)))
        = -(Real.log 5 - Real.log (1 / lam) + ‖Complex.log m‖ / 2) := by
      rw [one_div, Real.log_inv]
      rw [show 5 * lam * Real.exp (‖Complex.log m‖ / 2)
          = 5 * (lam * Real.exp (‖Complex.log m‖ / 2)) by ring]
      rw [Real.log_mul (by norm_num) (by positivity),
          Real.log_mul (ne_of_gt hlam) (Real.exp_ne_zero _), Real.log_exp]
      rw [one_div, Real.log_inv]
      ring
    linarith [h1, h2]
  have hlognn : 0 ≤ Real.log (1 / lam) := by
    rw [one_div, Real.log_inv]
    linarith [Real.log_nonpos hlam.le hlam1]
  have hlog5 : Real.log 5 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5); linarith
  have habs : |Real.log ‖Complex.sinh (a * u) / a‖|
      ≤ Real.log (1 / lam) + ‖Complex.log m‖ / 2 + Real.log 5 := by
    rw [abs_le]
    have hlog5nn : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    constructor
    · linarith [hlog_dn, hlognn, hlogm_pos]
    · linarith [hlog_up, hlog5nn]
  have hlogy : ‖Complex.log (Complex.sinh (a * u) / a)‖
      ≤ Real.log (1 / lam) + ‖Complex.log m‖ / 2 + 9 := by
    calc ‖Complex.log (Complex.sinh (a * u) / a)‖
        ≤ |(Complex.log (Complex.sinh (a * u) / a)).re|
          + |(Complex.log (Complex.sinh (a * u) / a)).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |Real.log ‖Complex.sinh (a * u) / a‖|
          + |(Complex.sinh (a * u) / a).arg| := by rw [Complex.log_re, Complex.log_im]
      _ ≤ (Real.log (1 / lam) + ‖Complex.log m‖ / 2 + Real.log 5) + Real.pi :=
          add_le_add habs (Complex.abs_arg_le_pi _)
      _ ≤ Real.log (1 / lam) + ‖Complex.log m‖ / 2 + 9 := by
          have h1 := Real.pi_lt_four
          linarith
  have hkey : 1 / (20 * lam) ≤ ‖u‖ - K * (‖Complex.log m‖ / 2) := by
    rw [hu_norm]
    have h2 : 1 / (20 * lam) ≤ ‖Complex.log m‖ / (4 * lam) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hlogm, hlam]
    have h3 : K * (‖Complex.log m‖ / 2) ≤ ‖Complex.log m‖ / (4 * lam) := by
      calc K * (‖Complex.log m‖ / 2) ≤ (1 / (2 * lam)) * (‖Complex.log m‖ / 2) :=
            mul_le_mul_of_nonneg_right hKlam (by positivity)
        _ = ‖Complex.log m‖ / (4 * lam) := by ring
    have h4 : ‖Complex.log m‖ / (2 * lam)
        = ‖Complex.log m‖ / (4 * lam) + ‖Complex.log m‖ / (4 * lam) := by
      field_simp
      ring
    linarith [h2, h3, h4]
  have hdec : Work.Implosion.approxEcal a κ u
      = u + κ * Complex.log (Complex.sinh (a * u) / a) := Work.Implosion.approxEcal_apply a κ u
  have htri : ‖u‖ - ‖κ * Complex.log (Complex.sinh (a * u) / a)‖
      ≤ ‖Work.Implosion.approxEcal a κ u‖ := by
    have h := norm_sub_le (u + κ * Complex.log (Complex.sinh (a * u) / a))
      (κ * Complex.log (Complex.sinh (a * u) / a))
    rw [add_sub_cancel_right] at h
    rw [hdec]
    linarith [h]
  have hstep : ‖u‖ - K * (Real.log (1 / lam) + ‖Complex.log m‖ / 2 + 9)
      ≤ ‖u‖ - ‖κ * Complex.log (Complex.sinh (a * u) / a)‖ := by
    rw [norm_mul]
    have h3 : ‖κ‖ * ‖Complex.log (Complex.sinh (a * u) / a)‖
        ≤ K * (Real.log (1 / lam) + ‖Complex.log m‖ / 2 + 9) :=
      mul_le_mul hκ hlogy (norm_nonneg _) hK
    linarith
  have hfinal : 1 / (20 * lam) - K * (Real.log (1 / lam) + 9)
      ≤ ‖Work.Implosion.approxEcal a κ u‖ := by
    linarith [htri, hstep, hkey]
  rw [hadef] at hfinal
  exact hfinal

/-! ## §5 The threshold and the landing of the exit window -/

/-- **Monotonicity of the level function `λ ↦ 1/(20λ) − K(log (1/λ) + 9)`** for
`λ ≤ θ ≤ 1/(20K)`: the identity `1/(20λ) − 1/(20θ) = (θ−λ)/(20λθ)` and `log (θ/λ) ≤ θ/λ − 1`
give `g λ − g θ ≥ (θ−λ)(1/(20θ) − K)/λ ≥ 0`. -/
theorem level_g_mono {K θ lam : ℝ} (hθ : 0 < θ) (hθK : θ ≤ 1 / (20 * K))
    (hlam : 0 < lam) (hle : lam ≤ θ) :
    1 / (20 * θ) - K * (Real.log (1 / θ) + 9)
      ≤ 1 / (20 * lam) - K * (Real.log (1 / lam) + 9) := by
  have hKpos : 0 < K := by
    by_contra h
    push Not at h
    have h1 : (1 : ℝ) / (20 * K) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith)
    linarith [hθK, hθ]
  have hKle : K ≤ 1 / (20 * θ) := by
    rw [le_div_iff₀ (by positivity)]
    have h2 := mul_le_mul_of_nonneg_left hθK (by positivity : (0 : ℝ) ≤ 20 * K)
    rw [mul_one_div, div_self (by positivity : 20 * K ≠ 0)] at h2
    linarith [h2]
  have h1 : 1 / (20 * lam) - 1 / (20 * θ) = (θ - lam) / (20 * lam * θ) := by
    field_simp
  have h2 : Real.log (θ / lam) ≤ θ / lam - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2' : K * Real.log (θ / lam) ≤ K * (θ / lam - 1) :=
    mul_le_mul_of_nonneg_left h2 hKpos.le
  have h3 : Real.log (1 / lam) - Real.log (1 / θ) = Real.log (θ / lam) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv,
        Real.log_div (ne_of_gt hθ) (ne_of_gt hlam)]
    ring
  have h3' : K * Real.log (1 / lam) - K * Real.log (1 / θ) = K * Real.log (θ / lam) := by
    rw [← mul_sub, h3]
  have h4 : (θ - lam) / (20 * lam * θ) - K * (θ / lam - 1)
      = (θ - lam) * (1 / (20 * θ) - K) / lam := by
    field_simp
  have h5 : 0 ≤ (θ - lam) * (1 / (20 * θ) - K) / lam := by
    apply div_nonneg _ hlam.le
    exact mul_nonneg (by linarith) (by linarith)
  linarith [h1, h2', h3', h4, h5]

/-- **The level at the threshold `θ = 1/(100 (R+K+1)²)` exceeds `2R`.**  Indeed
`1/(20θ) = 5(R+K+1)²` and `log (1/θ) = log (100 (R+K+1)²) ≤ 20 (R+K+1)`, so for `R ≥ 4K+4`
the difference is at least `25K² + 133K + 117 > 0`. -/
theorem level_at_theta {R K : ℝ} (hK : 0 ≤ K) (hR4K : R ≥ 4 * K + 4) :
    2 * R < 1 / (20 * (1 / (100 * (R + K + 1) ^ 2)))
      - K * (Real.log (1 / (1 / (100 * (R + K + 1) ^ 2))) + 9) := by
  set S : ℝ := R + K + 1 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; linarith
  have hS1 : 1 ≤ S := by rw [hSdef]; linarith
  have h100 : 0 < 100 * S ^ 2 := by positivity
  have h1 : 1 / (20 * (1 / (100 * S ^ 2))) = 5 * S ^ 2 := by
    field_simp
    ring
  have h2 : Real.log (1 / (1 / (100 * S ^ 2))) = Real.log (100 * S ^ 2) := by
    congr 1
    field_simp
  have h3 : Real.log (100 * S ^ 2) ≤ 2 * S + 97 := by
    have h4 : Real.log (100 * S ^ 2) = Real.log 100 + Real.log (S ^ 2) := by
      rw [Real.log_mul (by norm_num) (by positivity)]
    have h5 : Real.log (S ^ 2) = 2 * Real.log S := by rw [Real.log_pow]; norm_num
    have h6 : Real.log S ≤ S - 1 := Real.log_le_sub_one_of_pos hSpos
    have h7 : Real.log 100 ≤ 99 := by
      have h8 : Real.log 100 ≤ 100 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith
    rw [h4, h5]
    linarith
  have h11 : -(K * (Real.log (100 * S ^ 2) + 9)) ≥ -(K * (2 * S + 106)) := by
    have h12 : K * (Real.log (100 * S ^ 2) + 9) ≤ K * (2 * S + 106) := by
      apply mul_le_mul_of_nonneg_left _ hK
      linarith
    linarith
  rw [h1, h2]
  nlinarith [h11, hR4K, hK, hSdef]

/-- **`Work.PARIMPL2.LavaursA.exit_zeta_lo`.**  There is `R₀ > 0` such that for every depth
`R ≥ R₀` and every width `H` with `R ≥ 8(H+1)`, on a ball of parameters `c ∈ P.Nm` around `c₀`
the following holds: if the chart coordinate `ζ = chartZeta P c z` is small (`‖ζ‖ ≤ 4/R`,
`Re ζ > 0`) and the point lies in the *outgoing* window (`Re (approxU P c z) ∈ [R, R+2]`,
`|Im (approxU P c z)| ≤ H`), then `‖ζ‖ ≥ 1/(4R)`.

This is the level estimate that makes the outgoing (repelling) end of the transit match the
Écalle coordinate `1/ζ`: the window `Re Ũ ∈ [R, R+2]` sits at `‖ζ‖ ≈ 1/R`. -/
theorem exit_zeta_lo {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R ≥ R₀, ∀ H : ℝ, R ≥ 8 * (H + 1) → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ, ∀ z : ℂ,
        ‖Work.PARIMPL.chartZeta P c z‖ ≤ 4 / R →
        0 < (Work.PARIMPL.chartZeta P c z).re →
        (Work.PARIMPL.approxU P c z).re ∈ Set.Icc R (R + 2) →
        |(Work.PARIMPL.approxU P c z).im| ≤ H →
        1 / (4 * R) ≤ ‖Work.PARIMPL.chartZeta P c z‖ := by
  set K : ℝ := ‖P.κ c₀‖ + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hK0 : 0 ≤ K := hKpos.le
  refine ⟨max 8 (max (12 * K ^ 2 + 22 * K + 8) (4 * K + 4)), by positivity, ?_⟩
  intro R hR H hRH
  have hR8 : 8 ≤ R := le_trans (le_max_left _ _) hR
  have hRlevel : R ≥ 12 * K ^ 2 + 22 * K + 8 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hR4K : R ≥ 4 * K + 4 :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR
  set S : ℝ := R + K + 1 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; linarith
  set θ : ℝ := 1 / (100 * S ^ 2) with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one (by positivity)]
    nlinarith [hSpos]
  have hθK : θ ≤ 1 / (20 * K) := by
    rw [hθdef, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hK0, hSpos, hSdef, hR4K]
  have hθ20θ : K ≤ 1 / (20 * θ) := by
    rw [le_div_iff₀ (by positivity)]
    have h2 := mul_le_mul_of_nonneg_left hθK (by positivity : (0 : ℝ) ≤ 20 * K)
    have h3 : 20 * K * (1 / (20 * K)) = 1 := by
      rw [mul_one_div, div_self (by positivity : (20 : ℝ) * K ≠ 0)]
    linarith [h2, h3]
  have hθR := level_at_theta hK0 hR4K
  have hθreq : 1 / (20 * θ) - K * (Real.log (1 / θ) + 9)
      = 1 / (20 * (1 / (100 * S ^ 2))) - K * (Real.log (1 / (1 / (100 * S ^ 2))) + 9) := by
    rw [hθdef]
  -- the two parameter radii
  obtain ⟨ρκ, hρκpos, hκρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : ℂ, ‖c - c₀‖ < ρ →
      ‖P.κ c - P.κ c₀‖ ≤ 1 := by
    have hcont : ContinuousAt P.κ c₀ :=
      P.cont_κ.continuousAt (Metric.ball_mem_nhds c₀ P.hρ₀)
    obtain ⟨ρ, hρ, hρ'⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
    refine ⟨ρ, hρ, fun c hc => ?_⟩
    have h1 : dist c c₀ < ρ := by simpa [dist_eq_norm] using hc
    have h2 := hρ' h1
    simpa [dist_eq_norm] using le_of_lt h2
  obtain ⟨ρ_lam, hρ_lam_pos, h_lam_ρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
      P.lam c ≤ θ := by
    have h : Tendsto P.lam (𝓝[P.Nm] c₀) (𝓝 0) :=
      P.tendsto_lam c₀ P.a2₀ (by simpa using P.hρ₀)
    have hev : ∀ᶠ c in 𝓝[P.Nm] c₀, P.lam c ≤ θ := h.eventually (Iic_mem_nhds hθpos)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨ρ, hρ, hρ'⟩ := hev
    exact ⟨ρ, hρ, fun c hc => hρ' (by simpa [Metric.mem_ball] using hc.2) hc.1⟩
  refine ⟨min (min P.ρ₀ ρκ) ρ_lam, lt_min (lt_min P.hρ₀ hρκpos) hρ_lam_pos, ?_⟩
  intro c hc z hzle hzre hzur hzuim
  have hcNm : c ∈ P.Nm := hc.1
  have hcb : c ∈ Metric.ball c₀ ρ_lam := by
    have h1 : Metric.ball c₀ (min (min P.ρ₀ ρκ) ρ_lam) ⊆ Metric.ball c₀ ρ_lam :=
      Metric.ball_subset_ball (min_le_right _ _)
    exact h1 hc.2
  have hlam_pos : 0 < P.lam c := P.lam_pos_of_mem_Nm hcNm
  have hlam_le : P.lam c ≤ θ := h_lam_ρ c ⟨hcNm, hcb⟩
  have ha : P.a c = (P.lam c : ℂ) * Complex.I := P.a_of_mem_Nm hcNm
  have ha_norm : ‖P.a c‖ = P.lam c := by
    rw [ha, norm_mul, Complex.norm_I, mul_one]
    simp [abs_of_pos hlam_pos]
  have ha_ne : P.a c ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha_norm
    linarith [hlam_pos]
  have hκc : ‖P.κ c‖ ≤ K := by
    have h1 : ‖P.κ c - P.κ c₀‖ ≤ 1 := hκρ c (by
      have h2 : Metric.ball c₀ (min (min P.ρ₀ ρκ) ρ_lam) ⊆ Metric.ball c₀ ρκ :=
        Metric.ball_subset_ball (le_trans (min_le_left (min P.ρ₀ ρκ) ρ_lam)
          (min_le_right P.ρ₀ ρκ))
      have h3 : c ∈ Metric.ball c₀ ρκ := h2 hc.2
      simpa [dist_eq_norm] using h3)
    have h4 : P.κ c = P.κ c₀ + (P.κ c - P.κ c₀) := by ring
    rw [h4] at ⊢
    calc ‖P.κ c₀ + (P.κ c - P.κ c₀)‖ ≤ ‖P.κ c₀‖ + ‖P.κ c - P.κ c₀‖ := norm_add_le _ _
      _ ≤ ‖P.κ c₀‖ + 1 := by linarith
      _ = K := by rw [hKdef]
  set ζ : ℂ := Work.PARIMPL.chartZeta P c z with hζdef
  have hζle : ‖ζ‖ ≤ 4 / R := by rw [hζdef]; exact hzle
  have hζre : 0 < ζ.re := by rw [hζdef]; exact hzre
  have hζ1 : ‖ζ‖ ≤ 1 := by
    have h1 : 4 / R ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hzeta4 : ‖ζ‖ ≤ 4 / R := hζle
  have hu : Work.PARIMPL.approxU P c z = Work.Implosion.approxEcal (P.a c) (P.κ c)
      (Work.Implosion.ecalCoord (P.a c) ζ) := rfl
  by_cases hcase : 4 * P.lam c ≤ ‖ζ‖
  · -- regime I: the chart coordinate is not small compared to `|a|`
    have hcase' : 4 * ‖P.a c‖ ≤ ‖ζ‖ := by rw [ha_norm]; exact hcase
    have hdec : ‖Work.Implosion.approxEcal (P.a c) (P.κ c)
        (Work.Implosion.ecalCoord (P.a c) ζ) - 1 / ζ‖
        ≤ 1 / (36 * ‖ζ‖) + K * (Real.log (1 / ‖ζ‖) + 6) := by
      have h0 := approxEcal_sub_inv_le (κ := P.κ c) ha_ne hζre hζ1 hcase'
      have hlog0 : 0 ≤ Real.log (1 / ‖ζ‖) + 6 := by
        have h1 : 0 ≤ Real.log (1 / ‖ζ‖) := Real.log_nonneg (by
          rw [le_div_iff₀ (lt_of_lt_of_le hζre (Complex.re_le_norm ζ))]
          linarith [hζ1])
        linarith
      calc ‖Work.Implosion.approxEcal (P.a c) (P.κ c)
            (Work.Implosion.ecalCoord (P.a c) ζ) - 1 / ζ‖
          ≤ 1 / (36 * ‖ζ‖) + ‖P.κ c‖ * (Real.log (1 / ‖ζ‖) + 6) := h0
        _ ≤ 1 / (36 * ‖ζ‖) + K * (Real.log (1 / ‖ζ‖) + 6) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right hκc hlog0)
    rw [← hu] at hdec
    exact zeta_level_core hRH hK0 hκc hζre hdec hzur hzuim hRlevel
  · -- regime II: the chart coordinate is small compared with `|a|`
    have hlt : ‖ζ‖ < 4 * P.lam c := not_le.mp hcase
    have hlam1 : P.lam c ≤ 1 := le_trans hlam_le hθ1
    have hKlam : K ≤ 1 / (2 * P.lam c) := by
      have h1 : 1 / (2 * θ) ≤ 1 / (2 * P.lam c) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h2 : K ≤ 1 / (2 * θ) := le_trans hθ20θ (by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith)
      linarith
    have hC := approxEcal_norm_ge_of_small_zeta hlam_pos hlam1 hK0 hκc hKlam hζre hlt
    have hnorm : ‖Work.Implosion.approxEcal ((P.lam c : ℂ) * Complex.I) (P.κ c)
        (Work.Implosion.ecalCoord ((P.lam c : ℂ) * Complex.I) ζ)‖
        = ‖Work.PARIMPL.approxU P c z‖ := by
      rw [hu, ha]
    rw [hnorm] at hC
    have hmono := level_g_mono hθpos hθK hlam_pos hlam_le
    have hub : ‖Work.PARIMPL.approxU P c z‖ ≤ 2 * R := by
      have h1 : ‖Work.PARIMPL.approxU P c z‖ ≤ |(Work.PARIMPL.approxU P c z).re|
          + |(Work.PARIMPL.approxU P c z).im| := Complex.norm_le_abs_re_add_abs_im _
      have h2 : |(Work.PARIMPL.approxU P c z).re| ≤ R + 2 := by
        rw [abs_of_nonneg (by linarith [hzur.1])]
        exact hzur.2
      have h3 : H ≤ R / 8 - 1 := by linarith
      linarith
    rw [hθreq] at hθR
    linarith

end Work.PARIMPL2.LavaursA
