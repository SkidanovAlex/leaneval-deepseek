import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Windows
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.approxEcal_end_out_small
import Submission.Work.PARIMPL2.coord_in_of_estimates

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

open Work.PARIMPL (ParNormal chartZeta approxU ecalU)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## §1 The limiting chart coordinate

`zeta0 P z = (z - d.z₁)/P.s c₀ = -1/(w0 P z)`: the value that the chart coordinate
`chartZeta P c z' = (z' - P.m c)/P.s c` approaches as `c → c₀` and `z' → z`.  All the
estimates of `wout_model` are stated against it, because `wout_model`'s right-hand side
`-approxCoordRep κ₀ (w0 P z)` is exactly `1/(zeta0 P z) - κ₀ log (zeta0 P z)`. -/

/-- The limiting chart coordinate of the point `z` in the `c₀`-chart. -/
noncomputable def zeta0 (P : ParNormal d) (z : ℂ) : ℂ := (z - d.z₁) / P.s c₀

theorem zeta0_apply (P : ParNormal d) (z : ℂ) : zeta0 P z = (z - d.z₁) / P.s c₀ := rfl

/-- The `c₀`-chart coordinate `w0 P z` is the negative reciprocal of `zeta0 P z`. -/
theorem w0_eq_neg_inv_zeta0 (P : ParNormal d) {z : ℂ} (hz : z ≠ d.z₁) :
    Work.PARIMPL2.w0 P z = -(zeta0 P z)⁻¹ := by
  have hs : P.s c₀ ≠ 0 := P.s_ne c₀ (mem_ball_self P.hρ₀)
  have hz1 : z - d.z₁ ≠ 0 := sub_ne_zero.mpr hz
  rw [Work.PARIMPL2.w0, zeta0]
  field_simp

/-! ## §2 Bounds on the outgoing window `WoutG` -/

/-- The elementary bound on a point of the outgoing geometric window: the `c₀`-chart
coordinate `w = w0 P z` has real part in `[-(R+2), -R]` and imaginary part bounded by `H`,
hence `R ≤ ‖w‖ ≤ R + H + 2`. -/
theorem woutG_w0_bounds {P : ParNormal d} {R H : ℝ} (hR : 0 < R) (hH : 0 ≤ H) {z : ℂ}
    (hz : z ∈ Work.PARIMPL2.WoutG P R H) :
    |(Work.PARIMPL2.w0 P z).re| ≤ R + 2 ∧ |(Work.PARIMPL2.w0 P z).im| ≤ H ∧
      R ≤ ‖Work.PARIMPL2.w0 P z‖ ∧ ‖Work.PARIMPL2.w0 P z‖ ≤ R + H + 2 := by
  obtain ⟨hz1, hre, him⟩ := hz
  obtain ⟨hre1, hre2⟩ := hre
  have habs : |(Work.PARIMPL2.w0 P z).re| ≤ R + 2 := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  refine ⟨habs, him, ?_, ?_⟩
  · calc R ≤ -((Work.PARIMPL2.w0 P z).re) := by linarith
      _ ≤ |(Work.PARIMPL2.w0 P z).re| := neg_le_abs _
      _ ≤ ‖Work.PARIMPL2.w0 P z‖ := Complex.abs_re_le_norm _
  · have hsq : ‖Work.PARIMPL2.w0 P z‖ ^ 2 ≤ (R + H + 2) ^ 2 := by
      have h1 : (Work.PARIMPL2.w0 P z).re ^ 2 ≤ (R + 2) ^ 2 := by
        have hb := abs_le.mp habs
        nlinarith [hb.1, hb.2, hR]
      have h2 : (Work.PARIMPL2.w0 P z).im ^ 2 ≤ H ^ 2 := by
        have hb := abs_le.mp him
        nlinarith [hb.1, hb.2, hH]
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [hre2, h1, h2, hR, hH]
    nlinarith [hsq, norm_nonneg (Work.PARIMPL2.w0 P z), hre2, him,
      abs_nonneg (Work.PARIMPL2.w0 P z).im, hR, hH]

/-- The window sits at distance `≤ ‖P.s c₀‖/R` from the parabolic point `d.z₁`. -/
theorem norm_sub_z₁_le {P : ParNormal d} {R H : ℝ} (hR : 0 < R) (hH : 0 ≤ H) {z : ℂ}
    (hz : z ∈ Work.PARIMPL2.WoutG P R H) :
    ‖z - d.z₁‖ ≤ ‖P.s c₀‖ / R := by
  have hz1 : z ≠ d.z₁ := hz.1
  have hs : P.s c₀ ≠ 0 := P.s_ne c₀ (mem_ball_self P.hρ₀)
  have hz1ne : z - d.z₁ ≠ 0 := sub_ne_zero.mpr hz1
  have hlow : R ≤ ‖Work.PARIMPL2.w0 P z‖ := (woutG_w0_bounds hR hH hz).2.2.1
  have hw0 : Work.PARIMPL2.w0 P z = -P.s c₀ / (z - d.z₁) := rfl
  have hmul : (z - d.z₁) * Work.PARIMPL2.w0 P z = -P.s c₀ := by
    rw [hw0]
    field_simp
  have hn : ‖z - d.z₁‖ * ‖Work.PARIMPL2.w0 P z‖ = ‖P.s c₀‖ := by
    rw [← norm_mul, hmul, norm_neg]
  rw [le_div_iff₀ hR]
  calc ‖z - d.z₁‖ * R ≤ ‖z - d.z₁‖ * ‖Work.PARIMPL2.w0 P z‖ :=
        mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
    _ = ‖P.s c₀‖ := hn

/-- `‖ζ₀‖ ≤ 1/R` on the outgoing window. -/
theorem norm_zeta0_le {P : ParNormal d} {R H : ℝ} (hR : 0 < R) (hH : 0 ≤ H) {z : ℂ}
    (hz : z ∈ Work.PARIMPL2.WoutG P R H) : ‖zeta0 P z‖ ≤ 1 / R := by
  have hle : R ≤ ‖Work.PARIMPL2.w0 P z‖ := (woutG_w0_bounds hR hH hz).2.2.1
  have heq : zeta0 P z = (-(Work.PARIMPL2.w0 P z))⁻¹ := by
    have h := w0_eq_neg_inv_zeta0 P hz.1
    rw [h, neg_neg, inv_inv]
  rw [heq, norm_inv, norm_neg, one_div]
  exact (inv_le_inv₀ (lt_of_lt_of_le hR hle) hR).mpr hle

/-- `Re ζ₀ ≥ R/(R+H+2)²` on the outgoing window: `ζ₀ = -1/w` and `Re w ≤ -R`,
`‖w‖ ≤ R+H+2`. -/
theorem re_zeta0_ge {P : ParNormal d} {R H : ℝ} (hR : 0 < R) (hH : 0 ≤ H) {z : ℂ}
    (hz : z ∈ Work.PARIMPL2.WoutG P R H) :
    R / (R + H + 2) ^ 2 ≤ (zeta0 P z).re := by
  obtain ⟨-, -, hlow, hup⟩ := woutG_w0_bounds hR hH hz
  have hre : (Work.PARIMPL2.w0 P z).re ≤ -R := hz.2.1.2
  have heq : zeta0 P z = (-(Work.PARIMPL2.w0 P z))⁻¹ := by
    have h := w0_eq_neg_inv_zeta0 P hz.1
    rw [h, neg_neg, inv_inv]
  rw [heq, Complex.inv_re, Complex.normSq_eq_norm_sq, Complex.neg_re, norm_neg]
  have hx : 0 < ‖Work.PARIMPL2.w0 P z‖ ^ 2 := by nlinarith [hlow, hR]
  have hy : 0 < (R + H + 2) ^ 2 := by
    have h1 : 0 < R + H + 2 := by linarith
    positivity
  have h1 : R / (R + H + 2) ^ 2 ≤ R / ‖Work.PARIMPL2.w0 P z‖ ^ 2 := by
    rw [div_le_div_iff₀ hy hx]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hup 2) hR.le
  have h2 : R / ‖Work.PARIMPL2.w0 P z‖ ^ 2 ≤ (-(Work.PARIMPL2.w0 P z).re) / ‖Work.PARIMPL2.w0 P z‖ ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

/-! ## §3 The uniform continuity of the model coordinate on the compact window set -/

/-- **The model coordinate depends uniformly continuously on `(ζ, κ)`** on the compact set
`{reLo ≤ Re ζ} ∩ B(0, 1/4)` of chart values and the `κ`-ball `B(κ₀, 1)`: for every `ε`
there is `δ` with
`‖1/ζ - κ log ζ - (1/ζ' - κ' log ζ')‖ ≤ ε`
whenever `‖ζ - ζ'‖ < δ`, `‖κ - κ'‖ < δ` and both `(ζ,κ)`, `(ζ',κ')` lie in the set.  (For
`reLo ≤ Re ζ ≤ ‖ζ‖ ≤ 1/4` the point `ζ` lies in the slit plane, so `Complex.log` is
continuous there.) -/
theorem uniform_model_coord {reLo : ℝ} (hreLo : 0 < reLo) (κ₀ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p q : ℂ × ℂ,
      reLo ≤ p.1.re → ‖p.1‖ ≤ 1 / 4 → reLo ≤ q.1.re → ‖q.1‖ ≤ 1 / 4 →
      ‖p.2 - κ₀‖ ≤ 1 → ‖q.2 - κ₀‖ ≤ 1 → dist p q < δ →
      dist (p.1⁻¹ - p.2 * Complex.log p.1) (q.1⁻¹ - q.2 * Complex.log q.1) < ε := by
  have hKc : IsCompact ({ζ : ℂ | reLo ≤ ζ.re} ∩ closedBall (0 : ℂ) (1 / 4)) :=
    (isCompact_closedBall (0 : ℂ) (1 / 4)).inter_left
      (isClosed_le continuous_const Complex.continuous_re)
  have hK : IsCompact (({ζ : ℂ | reLo ≤ ζ.re} ∩ closedBall (0 : ℂ) (1 / 4)) ×ˢ
      closedBall κ₀ 1) := hKc.prod (isCompact_closedBall κ₀ 1)
  have hcon : ContinuousOn (fun p : ℂ × ℂ => p.1⁻¹ - p.2 * Complex.log p.1)
      (({ζ : ℂ | reLo ≤ ζ.re} ∩ closedBall (0 : ℂ) (1 / 4)) ×ˢ closedBall κ₀ 1) := by
    refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.inv₀ (continuous_fst.continuousOn) ?_
      intro p hp
      have hp1 : reLo ≤ p.1.re := hp.1.1
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hreLo (le_trans hp1 (Complex.re_le_norm _))))
    · refine ContinuousOn.mul (continuous_snd.continuousOn) ?_
      refine ContinuousOn.clog (continuous_fst.continuousOn) ?_
      intro p hp
      have hp1 : reLo ≤ p.1.re := hp.1.1
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le hreLo hp1))
  obtain ⟨δ, hδ, hδ'⟩ :=
    (Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hcon)) ε hε
  refine ⟨δ, hδ, fun p q hp1 hp2 hp3 hp4 hp5 hp6 hd => ?_⟩
  exact hδ' p ⟨⟨hp1, by rw [Metric.mem_closedBall, dist_zero_right]; exact hp2⟩,
      by rw [Metric.mem_closedBall, dist_eq_norm]; exact hp5⟩
    q ⟨⟨hp3, by rw [Metric.mem_closedBall, dist_zero_right]; exact hp4⟩,
      by rw [Metric.mem_closedBall, dist_eq_norm]; exact hp6⟩ hd

/-! ## §4 The slit-plane condition at the outgoing end -/

/-- **The slit-plane condition is automatic at the outgoing end.**  If `ζ` is small with
`reLo ≤ Re ζ ≤ ‖ζ‖ ≤ 1/4`, `4‖a‖ ≤ ‖ζ‖` and `‖a‖² ≤ reLo⁴`, then the logarithm argument
`sinh (a·u)/a` of the approximate Écalle coordinate (`u = ecalCoord a ζ`) has **positive real
part**: `sinh (a·u)/a = cosh (a·u)/ζ` and `cosh (a·u) = 1 + O(‖a‖²/‖ζ‖²)` while
`Re (1/ζ) ≥ 16 reLo`. -/
theorem slit_of_small_a {a ζ : ℂ} (ha : a ≠ 0) {reLo : ℝ} (hreLo : 0 < reLo)
    (hre : reLo ≤ ζ.re) (hζle : ‖ζ‖ ≤ 1 / 4) (haζ : 4 * ‖a‖ ≤ ‖ζ‖)
    (ha2 : ‖a‖ ^ 2 ≤ reLo ^ 4) :
    Complex.sinh (a * Work.Implosion.ecalCoord a ζ) / a ∈ Complex.slitPlane := by
  have hζpos : 0 < ‖ζ‖ := lt_of_lt_of_le (lt_of_lt_of_le hreLo hre) (Complex.re_le_norm ζ)
  have hζne : ζ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hζpos)
  have ha_lt : ‖a‖ < ‖ζ‖ := by linarith
  have hζa : ζ ≠ a := by intro h; rw [h] at ha_lt; exact lt_irrefl _ ha_lt
  have hζna : ζ ≠ -a := by intro h; rw [h, norm_neg] at ha_lt; exact lt_irrefl _ ha_lt
  rw [Work.PARIMPL2.sinh_div_eq_cosh_div ha hζne hζa hζna]
  have hu_bd : ‖Work.Implosion.ecalCoord a ζ - 1 / ζ‖ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 :=
    Work.PARIMPL2.ecalCoord_sub_inv_le_small a ζ ha hζne haζ
  have hζsq : ‖a‖ ^ 2 ≤ ‖ζ‖ ^ 2 / 16 := by nlinarith [haζ, norm_nonneg a, norm_nonneg ζ]
  have hterm : 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 ≤ 1 / (36 * ‖ζ‖) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hζsq, hζpos]
  have hu_le : ‖Work.Implosion.ecalCoord a ζ‖ ≤ 2 / ‖ζ‖ := by
    have h1 : ‖Work.Implosion.ecalCoord a ζ‖ ≤ ‖Work.Implosion.ecalCoord a ζ - 1 / ζ‖ + ‖(1 : ℂ) / ζ‖ := by
      calc ‖Work.Implosion.ecalCoord a ζ‖
          = ‖(Work.Implosion.ecalCoord a ζ - 1 / ζ) + 1 / ζ‖ := by ring_nf
        _ ≤ ‖Work.Implosion.ecalCoord a ζ - 1 / ζ‖ + ‖(1 : ℂ) / ζ‖ := norm_add_le _ _
    have h2 : ‖(1 : ℂ) / ζ‖ = 1 / ‖ζ‖ := by rw [norm_div, norm_one]
    rw [h2] at h1
    have h3 : 1 / (36 * ‖ζ‖) + 1 / ‖ζ‖ = 37 / (36 * ‖ζ‖) := by field_simp; ring
    have h4 : (37 : ℝ) / (36 * ‖ζ‖) ≤ 2 / ‖ζ‖ := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [hζpos]
    linarith [h1, hterm, hu_bd]
  have hau_le : ‖a * Work.Implosion.ecalCoord a ζ‖ ≤ 1 / 2 := by
    have ha4 : ‖a‖ ≤ ‖ζ‖ / 4 := by linarith
    rw [norm_mul]
    calc ‖a‖ * ‖Work.Implosion.ecalCoord a ζ‖ ≤ ‖a‖ * (2 / ‖ζ‖) :=
          mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
      _ ≤ (‖ζ‖ / 4) * (2 / ‖ζ‖) := mul_le_mul_of_nonneg_right ha4 (by positivity)
      _ = 1 / 2 := by field_simp; norm_num
  have hcosh : ‖Complex.cosh (a * Work.Implosion.ecalCoord a ζ) - 1‖ ≤
      ‖a * Work.Implosion.ecalCoord a ζ‖ ^ 2 := Work.PARIMPL2.cosh_sub_one_le (by linarith)
  have hcosh_le : ‖Complex.cosh (a * Work.Implosion.ecalCoord a ζ) - 1‖ ≤ ‖a‖ ^ 2 * 4 / ‖ζ‖ ^ 2 := by
    have ha2le : ‖a * Work.Implosion.ecalCoord a ζ‖ ≤ 2 * ‖a‖ / ‖ζ‖ := by
      rw [norm_mul]
      calc ‖a‖ * ‖Work.Implosion.ecalCoord a ζ‖ ≤ ‖a‖ * (2 / ‖ζ‖) :=
            mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
        _ = 2 * ‖a‖ / ‖ζ‖ := by ring
    calc ‖Complex.cosh (a * Work.Implosion.ecalCoord a ζ) - 1‖
        ≤ ‖a * Work.Implosion.ecalCoord a ζ‖ ^ 2 := hcosh
      _ ≤ (2 * ‖a‖ / ‖ζ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha2le 2
      _ = ‖a‖ ^ 2 * 4 / ‖ζ‖ ^ 2 := by ring
  have hcrux : 0 < (Complex.cosh (a * Work.Implosion.ecalCoord a ζ) / ζ).re := by
    rw [show Complex.cosh (a * Work.Implosion.ecalCoord a ζ) / ζ
        = 1 / ζ + (Complex.cosh (a * Work.Implosion.ecalCoord a ζ) - 1) / ζ by ring]
    rw [Complex.add_re]
    have hinv : 16 * reLo ≤ (1 / ζ).re := by
      rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq, le_div_iff₀ (by positivity)]
      have hζ2 : ‖ζ‖ ^ 2 ≤ 1 / 16 := by nlinarith [hζle, norm_nonneg ζ]
      calc 16 * reLo * ‖ζ‖ ^ 2 ≤ 16 * reLo * (1 / 16) :=
            mul_le_mul_of_nonneg_left hζ2 (by positivity)
        _ = reLo := by ring
        _ ≤ ζ.re := hre
    have herr : |((Complex.cosh (a * Work.Implosion.ecalCoord a ζ) - 1) / ζ).re| ≤ 4 * reLo := by
      have h3 : ‖(Complex.cosh (a * Work.Implosion.ecalCoord a ζ) - 1) / ζ‖ ≤ 4 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := by
        rw [norm_div]
        calc ‖Complex.cosh (a * Work.Implosion.ecalCoord a ζ) - 1‖ / ‖ζ‖
            ≤ (‖a‖ ^ 2 * 4 / ‖ζ‖ ^ 2) / ‖ζ‖ := div_le_div_of_nonneg_right hcosh_le (norm_nonneg _)
          _ = 4 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := by ring
      have h4 : 4 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 ≤ 4 * reLo := by
        rw [div_le_iff₀ (by positivity)]
        have hzn : reLo ≤ ‖ζ‖ := le_trans hre (Complex.re_le_norm ζ)
        have hζ3 : reLo ^ 3 ≤ ‖ζ‖ ^ 3 := pow_le_pow_left₀ hreLo.le hzn 3
        calc 4 * ‖a‖ ^ 2 ≤ 4 * reLo ^ 4 := by linarith [ha2]
          _ = 4 * reLo * reLo ^ 3 := by ring
          _ ≤ 4 * reLo * ‖ζ‖ ^ 3 := mul_le_mul_of_nonneg_left hζ3 (by linarith)
      refine le_trans (le_trans (Complex.abs_re_le_norm _) h3) h4
    have := neg_le_abs (((Complex.cosh (a * Work.Implosion.ecalCoord a ζ) - 1) / ζ).re)
    linarith
  exact Complex.mem_slitPlane_iff.mpr (Or.inl hcrux)

/-! ## §5 The chart drift `chartZeta P c z' → ζ₀ z` -/

/-- **The chart drift**: for `c` in the chart ball and `z'` within `A` of `z`, the chart
coordinate `chartZeta P c z'` differs from the limit `ζ₀ z` by at most `6A/‖P.s c₀‖`,
provided `‖P.m c - d.z₁‖ ≤ A`, `‖P.s c - P.s c₀‖ ≤ A` and `‖P.s c‖ ≥ ‖P.s c₀‖/2`. -/
theorem norm_chartZeta_sub_zeta0_le {P : ParNormal d} {R A : ℝ} (hR1 : 1 ≤ R) (hA : 0 < A)
    {c : ℂ} (hscne : P.s c ≠ 0)
    (hm : ‖P.m c - d.z₁‖ ≤ A) (hs : ‖P.s c - P.s c₀‖ ≤ A)
    (hs2 : ‖P.s c₀‖ / 2 ≤ ‖P.s c‖)
    {z z' : ℂ} (hz₁ : z ≠ d.z₁) (hzw : ‖z - d.z₁‖ ≤ ‖P.s c₀‖ / R)
    (hz' : ‖z' - z‖ ≤ A) :
    ‖chartZeta P c z' - zeta0 P z‖ ≤ 6 * A / ‖P.s c₀‖ := by
  have hs₀ : P.s c₀ ≠ 0 := P.s_ne c₀ (mem_ball_self P.hρ₀)
  have hs₀pos : 0 < ‖P.s c₀‖ := norm_pos_iff.mpr hs₀
  have hz1ne : z - d.z₁ ≠ 0 := sub_ne_zero.mpr hz₁
  have hkey : chartZeta P c z' - zeta0 P z
      = ((z' - z) * P.s c₀ + (z - d.z₁) * (P.s c₀ - P.s c) + (d.z₁ - P.m c) * P.s c₀)
        / (P.s c * P.s c₀) := by
    rw [chartZeta, zeta0]
    field_simp
    ring
  have hnum : ‖(z' - z) * P.s c₀ + (z - d.z₁) * (P.s c₀ - P.s c) + (d.z₁ - P.m c) * P.s c₀‖
      ≤ 3 * A * ‖P.s c₀‖ := by
    have hRinv : (1 : ℝ) / R ≤ 1 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < R)]
      linarith
    have h1 : ‖(z' - z) * P.s c₀‖ ≤ A * ‖P.s c₀‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right hz' (norm_nonneg _)
    have h2 : ‖(z - d.z₁) * (P.s c₀ - P.s c)‖ ≤ A * ‖P.s c₀‖ := by
      rw [norm_mul, ← norm_sub_rev (P.s c) (P.s c₀)]
      calc ‖z - d.z₁‖ * ‖P.s c - P.s c₀‖ ≤ (‖P.s c₀‖ / R) * A :=
            mul_le_mul hzw (hs) (norm_nonneg _) (by positivity)
        _ ≤ A * ‖P.s c₀‖ := by
            have h2' : (‖P.s c₀‖ / R) * A ≤ A * ‖P.s c₀‖ := by
              calc (‖P.s c₀‖ / R) * A = (1 / R) * (A * ‖P.s c₀‖) := by ring
                _ ≤ A * ‖P.s c₀‖ := mul_le_of_le_one_left (by positivity) hRinv
            exact h2'
    have h3 : ‖(d.z₁ - P.m c) * P.s c₀‖ ≤ A * ‖P.s c₀‖ := by
      rw [norm_mul, ← norm_sub_rev (P.m c) (d.z₁)]
      exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    calc ‖(z' - z) * P.s c₀ + (z - d.z₁) * (P.s c₀ - P.s c) + (d.z₁ - P.m c) * P.s c₀‖
        ≤ ‖(z' - z) * P.s c₀‖ + ‖(z - d.z₁) * (P.s c₀ - P.s c)‖
          + ‖(d.z₁ - P.m c) * P.s c₀‖ := by
          calc ‖(z' - z) * P.s c₀ + (z - d.z₁) * (P.s c₀ - P.s c) + (d.z₁ - P.m c) * P.s c₀‖
              ≤ ‖(z' - z) * P.s c₀ + (z - d.z₁) * (P.s c₀ - P.s c)‖
                + ‖(d.z₁ - P.m c) * P.s c₀‖ := norm_add_le _ _
            _ ≤ (‖(z' - z) * P.s c₀‖ + ‖(z - d.z₁) * (P.s c₀ - P.s c)‖)
                + ‖(d.z₁ - P.m c) * P.s c₀‖ := by
                linarith [norm_add_le ((z' - z) * P.s c₀) ((z - d.z₁) * (P.s c₀ - P.s c))]
      _ ≤ 3 * A * ‖P.s c₀‖ := by linarith
  have hdenlow : ‖P.s c₀‖ / 2 * ‖P.s c₀‖ ≤ ‖P.s c‖ * ‖P.s c₀‖ :=
    mul_le_mul_of_nonneg_right hs2 (norm_nonneg _)
  have hdenpos : 0 < ‖P.s c₀‖ / 2 * ‖P.s c₀‖ := by positivity
  rw [hkey, norm_div, norm_mul]
  calc ‖(z' - z) * P.s c₀ + (z - d.z₁) * (P.s c₀ - P.s c) + (d.z₁ - P.m c) * P.s c₀‖
        / (‖P.s c‖ * ‖P.s c₀‖)
      ≤ (3 * A * ‖P.s c₀‖) / (‖P.s c‖ * ‖P.s c₀‖) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (3 * A * ‖P.s c₀‖) / (‖P.s c₀‖ / 2 * ‖P.s c₀‖) :=
        div_le_div_of_nonneg_left (by positivity) hdenpos hdenlow
    _ = 6 * A / ‖P.s c₀‖ := by
        field_simp
        ring

/-! ## §6 The outgoing model estimate -/

/-- **The outgoing model estimate on `WoutG` (design §3.4, L2).**  At fixed depth `R` (above the
chart threshold `RchOK`) and width `H` with `R ≥ 8(H+1)`, the outgoing approximate coordinate
`approxU P c z'` of the parameter `c` agrees, uniformly on the outgoing window and for `z'` close
to its point `z`, with `-approxCoordRep κ₀ (w0 z)`: on `WoutG` the chart value `ζ = -1/w0` has
`Re ζ > 0` and the outgoing asymptotics reads `approxEcal a κ (ecalCoord a ζ) = 1/ζ - κ log ζ`
(`Work.PARIMPL2.approxEcal_end_out_small`), whose limit at `ζ₀ = -1/(w0 z)` is
`-w0 + κ₀ log(-w0) = -approxCoordRep κ₀ (w0 z)`. -/
theorem wout_model {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (R H : ℝ) (hR : Work.PARIMPL2.RchOK P R) (hH : R ≥ 8 * (H + 1)) :
    ∀ ε > 0, ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ,
      ∀ z ∈ Work.PARIMPL2.WoutG P R H,
      ∀ z' : ℂ, ‖z' - z‖ ≤ δ →
        ‖Work.PARIMPL.approxU P c z' +
          Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P z)‖ ≤ ε := by
  intro ε hε
  by_cases hHneg : H < 0
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro c hc z hz z' hz'
    exfalso
    have h1 : |(Work.PARIMPL2.w0 P z).im| ≤ H := hz.2.2
    have h2 := abs_nonneg ((Work.PARIMPL2.w0 P z).im)
    linarith
  push_neg at hHneg
  have hR8 : 8 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hs₀ : P.s c₀ ≠ 0 := P.s_ne c₀ (mem_ball_self P.hρ₀)
  have hs₀pos : 0 < ‖P.s c₀‖ := norm_pos_iff.mpr hs₀
  have hc₀ball : c₀ ∈ ball c₀ P.ρ₀ := mem_ball_self P.hρ₀
  obtain ⟨C, hC0, hC⟩ := Work.PARIMPL2.approxEcal_end_out_small (‖P.κ c₀‖ + 1) (by positivity)
  set reLo : ℝ := R / (R + H + 2) ^ 2 / 2 with hreLodef
  have hreLo : 0 < reLo := by rw [hreLodef]; positivity
  have hreLo2 : 2 * reLo = R / (R + H + 2) ^ 2 := by
    rw [hreLodef, mul_comm]
    exact div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)
  set lamMax : ℝ := min (reLo / 8) (min (reLo ^ 2) (Real.sqrt (ε * reLo ^ 3 / (2 * (C + 1)))))
    with hlamMaxdef
  have hlamMaxpos : 0 < lamMax := by
    rw [hlamMaxdef]
    exact lt_min (by positivity) (lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity)))
  have hlam_1 : lamMax ≤ reLo / 8 := le_trans (min_le_left _ _) le_rfl
  have hlam_2 : lamMax ≤ reLo ^ 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hlam_3 : lamMax ≤ Real.sqrt (ε * reLo ^ 3 / (2 * (C + 1))) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hlam_sq : lamMax ^ 2 ≤ ε * reLo ^ 3 / (2 * (C + 1)) := by
    have h1 : lamMax ^ 2 ≤ (Real.sqrt (ε * reLo ^ 3 / (2 * (C + 1)))) ^ 2 :=
      pow_le_pow_left₀ hlamMaxpos.le hlam_3 2
    rwa [Real.sq_sqrt (by positivity)] at h1
  have hmodel_bound : C * lamMax ^ 2 / reLo ^ 3 ≤ ε / 2 := by
    have hCa : C / (2 * (C + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (C + 1)) (by norm_num : (0 : ℝ) < 2)]
      linarith
    have h3 : C * lamMax ^ 2 ≤ C * (ε * reLo ^ 3 / (2 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hlam_sq hC0
    have h4 : C * (ε * reLo ^ 3 / (2 * (C + 1))) ≤ ε / 2 * reLo ^ 3 := by
      rw [show C * (ε * reLo ^ 3 / (2 * (C + 1))) = ε * reLo ^ 3 * (C / (2 * (C + 1))) by ring]
      calc ε * reLo ^ 3 * (C / (2 * (C + 1))) ≤ ε * reLo ^ 3 * (1 / 2) :=
            mul_le_mul_of_nonneg_left hCa (by positivity)
        _ = ε / 2 * reLo ^ 3 := by ring
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < reLo ^ 3)]
    linarith
  obtain ⟨d1, hd1pos, hunif⟩ :=
    uniform_model_coord (reLo := reLo) hreLo (P.κ c₀) (ε := ε / 2) (by linarith)
  set D : ℝ := min (d1 / 2) (min reLo (1 / 8)) with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact lt_min (by linarith) (lt_min hreLo (by norm_num))
  have hD₁ : D ≤ d1 / 2 := by rw [hDdef]; exact min_le_left _ _
  have hD₂ : D ≤ reLo := by rw [hDdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hD₃ : D ≤ 1 / 8 := by rw [hDdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  set A : ℝ := D * ‖P.s c₀‖ / 6 with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  obtain ⟨ρm, hρmpos, hmρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ ball c₀ ρ, ‖P.m c - d.z₁‖ ≤ A := by
    obtain ⟨δ, hδ, hδ'⟩ :=
      (continuousAt_iff.mp (P.cont_m.continuousAt (isOpen_ball.mem_nhds hc₀ball))) A hApos
    refine ⟨δ, hδ, fun c hc => ?_⟩
    have h1 : dist (P.m c) (P.m c₀) < A := hδ' (x := c) (by simpa [mem_ball] using hc)
    rw [P.m₀, dist_eq_norm] at h1
    exact le_of_lt h1
  obtain ⟨ρs, hρspos, hsρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ ball c₀ ρ,
      ‖P.s c - P.s c₀‖ ≤ A ∧ ‖P.s c₀‖ / 2 ≤ ‖P.s c‖ := by
    obtain ⟨δ, hδ, hδ'⟩ :=
      (continuousAt_iff.mp (P.cont_s.continuousAt (isOpen_ball.mem_nhds hc₀ball)))
        (min A (‖P.s c₀‖ / 2)) (by positivity)
    refine ⟨δ, hδ, fun c hc => ?_⟩
    have h1 : dist (P.s c) (P.s c₀) < min A (‖P.s c₀‖ / 2) :=
      hδ' (x := c) (by simpa [mem_ball] using hc)
    rw [dist_eq_norm] at h1
    have h2 : ‖P.s c - P.s c₀‖ ≤ A := le_trans (le_of_lt h1) (min_le_left _ _)
    have h3 : ‖P.s c₀‖ / 2 ≤ ‖P.s c‖ := by
      have h4 : ‖P.s c₀‖ - ‖P.s c‖ ≤ ‖P.s c₀ - P.s c‖ := by
        have habs := abs_le.mp (abs_norm_sub_norm_le (P.s c₀) (P.s c))
        linarith [habs.1]
      rw [norm_sub_rev (P.s c₀) (P.s c)] at h4
      have h5 : ‖P.s c - P.s c₀‖ < ‖P.s c₀‖ / 2 := lt_of_lt_of_le h1 (min_le_right _ _)
      linarith
    exact ⟨h2, h3⟩
  obtain ⟨ρκ, hρκpos, hκρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ ball c₀ ρ,
      ‖P.κ c - P.κ c₀‖ ≤ min (d1 / 2) 1 := by
    obtain ⟨δ, hδ, hδ'⟩ :=
      (continuousAt_iff.mp (P.cont_κ.continuousAt (isOpen_ball.mem_nhds hc₀ball)))
        (min (d1 / 2) 1) (by positivity)
    refine ⟨δ, hδ, fun c hc => ?_⟩
    have h1 : dist (P.κ c) (P.κ c₀) < min (d1 / 2) 1 := hδ' (x := c) (by simpa [mem_ball] using hc)
    rw [dist_eq_norm] at h1
    exact le_of_lt h1
  obtain ⟨rlam, hrlampos, hrlam⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ ball c₀ ρ, |P.a2 c| ≤ lamMax ^ 2 := by
    obtain ⟨δ, hδ, hδ'⟩ :=
      (continuousAt_iff.mp (P.cont_a2.continuousAt (isOpen_ball.mem_nhds hc₀ball)))
        (lamMax ^ 2) (by positivity)
    refine ⟨δ, hδ, fun c hc => ?_⟩
    have h1 : dist (P.a2 c) (P.a2 c₀) < lamMax ^ 2 := hδ' (x := c) (by simpa [mem_ball] using hc)
    rw [Real.dist_eq, P.a2₀, sub_zero] at h1
    exact le_of_lt h1
  have hlamc : ∀ c ∈ P.Nm ∩ ball c₀ rlam, P.lam c ≤ lamMax := by
    intro c hc
    have h1 : -(P.a2 c) ≤ lamMax ^ 2 := by
      have h2 := abs_le.mp (hrlam c hc.2)
      linarith [h2.1]
    rw [P.lam_eq_sqrt_of_mem_Nm hc.1]
    calc Real.sqrt (-(P.a2 c)) ≤ Real.sqrt (lamMax ^ 2) := Real.sqrt_le_sqrt h1
      _ = lamMax := Real.sqrt_sq hlamMaxpos.le
  refine ⟨min ρm (min ρs (min ρκ (min rlam 1))), A,
    lt_min hρmpos (lt_min hρspos (lt_min hρκpos (lt_min hrlampos one_pos))), hApos, ?_⟩
  intro c hc z hz z' hz'
  obtain ⟨hcNm, hcball⟩ := hc
  have hcρ₀ : c ∈ ball c₀ P.ρ₀ := hcNm.1
  have hcm : c ∈ ball c₀ ρm := by
    rw [mem_ball] at hcball ⊢
    exact lt_of_lt_of_le hcball (min_le_left _ _)
  have hcs : c ∈ ball c₀ ρs := by
    rw [mem_ball] at hcball ⊢
    exact lt_of_lt_of_le hcball (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcκ : c ∈ ball c₀ ρκ := by
    rw [mem_ball] at hcball ⊢
    exact lt_of_lt_of_le hcball (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hcrlam : c ∈ ball c₀ rlam := by
    rw [mem_ball] at hcball ⊢
    exact lt_of_lt_of_le hcball (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hlamle : P.lam c ≤ lamMax := hlamc c ⟨hcNm, hcrlam⟩
  have hlam_pos : 0 < P.lam c := P.lam_pos_of_mem_Nm hcNm
  have ha_ne : P.a c ≠ 0 := by
    rw [P.a_of_mem_Nm hcNm]
    exact mul_ne_zero (by exact_mod_cast ne_of_gt hlam_pos) Complex.I_ne_zero
  have hanorm : ‖P.a c‖ = P.lam c := by
    have h1 : ‖P.a c‖ ^ 2 = P.lam c ^ 2 := by
      rw [Complex.sq_norm, P.a_of_mem_Nm hcNm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have h2 : ‖P.a c‖ = |P.lam c| := by
      rw [← Real.sqrt_sq_eq_abs, ← h1, Real.sqrt_sq (norm_nonneg (P.a c))]
    rw [h2, abs_of_pos hlam_pos]
  have hzw : ‖z - d.z₁‖ ≤ ‖P.s c₀‖ / R := norm_sub_z₁_le hRpos hHneg hz
  have hζclose : ‖chartZeta P c z' - zeta0 P z‖ ≤ D := by
    have h : ‖chartZeta P c z' - zeta0 P z‖ ≤ 6 * A / ‖P.s c₀‖ :=
      norm_chartZeta_sub_zeta0_le (z := z) (z' := z') (c := c) hR1 hApos
        (P.s_ne c hcρ₀) (hmρ c hcm) (hsρ c hcs).1 (hsρ c hcs).2 hz.1 hzw hz'
    have h6 : 6 * A / ‖P.s c₀‖ = D := by
      rw [hAdef]
      field_simp
    rw [h6] at h
    exact h
  have hζ₀re2 : 2 * reLo ≤ (zeta0 P z).re := by
    have h := re_zeta0_ge hRpos hHneg hz
    linarith [hreLo2]
  have hζ₀norm : ‖zeta0 P z‖ ≤ 1 / 8 := by
    have h := norm_zeta0_le hRpos hHneg hz
    have h2 : (1 : ℝ) / R ≤ 1 / 8 := by
      rw [div_le_div_iff₀ hRpos (by norm_num)]
      linarith
    linarith
  have hζre : reLo ≤ (chartZeta P c z').re := by
    have h2 : |(chartZeta P c z').re - (zeta0 P z).re| ≤ ‖chartZeta P c z' - zeta0 P z‖ := by
      have h3 := Complex.abs_re_le_norm (chartZeta P c z' - zeta0 P z)
      rwa [Complex.sub_re] at h3
    have h3 := abs_le.mp h2
    linarith [h3.1, hζclose, hD₂, hζ₀re2]
  have hζnorm : ‖chartZeta P c z'‖ ≤ 1 / 4 := by
    have h2 : ‖chartZeta P c z'‖ ≤ ‖zeta0 P z‖ + ‖chartZeta P c z' - zeta0 P z‖ := by
      calc ‖chartZeta P c z'‖ = ‖(chartZeta P c z' - zeta0 P z) + zeta0 P z‖ := by ring_nf
        _ ≤ ‖chartZeta P c z' - zeta0 P z‖ + ‖zeta0 P z‖ := norm_add_le _ _
        _ = ‖zeta0 P z‖ + ‖chartZeta P c z' - zeta0 P z‖ := by ring
    linarith [hζ₀norm, hD₃]
  have h4a : 4 * ‖P.a c‖ ≤ ‖chartZeta P c z'‖ := by
    rw [hanorm]
    have h2 : 4 * P.lam c ≤ reLo / 2 := by
      have h := hlam_1
      nlinarith [hlamle, hlamMaxpos, hreLo]
    have h3 : reLo ≤ ‖chartZeta P c z'‖ := le_trans hζre (Complex.re_le_norm _)
    linarith
  have hζpos : 0 < (chartZeta P c z').re := lt_of_lt_of_le hreLo hζre
  have hζ4 : ‖chartZeta P c z'‖ ≤ 4 := by linarith
  have hslit : Complex.sinh (P.a c * Work.Implosion.ecalCoord (P.a c) (chartZeta P c z'))
      / P.a c ∈ Complex.slitPlane := by
    refine slit_of_small_a (a := P.a c) (ζ := chartZeta P c z') ha_ne hreLo hζre hζnorm h4a ?_
    rw [hanorm]
    have h1 : P.lam c ≤ reLo ^ 2 := le_trans hlamle hlam_2
    calc P.lam c ^ 2 ≤ (reLo ^ 2) ^ 2 := pow_le_pow_left₀ hlam_pos.le h1 2
      _ = reLo ^ 4 := by ring
  have hκK : ‖P.κ c‖ ≤ ‖P.κ c₀‖ + 1 := by
    have hκ1 : ‖P.κ c - P.κ c₀‖ ≤ 1 := le_trans (hκρ c hcκ) (min_le_right _ _)
    have h2 := norm_add_le (P.κ c - P.κ c₀) (P.κ c₀)
    rw [sub_add_cancel] at h2
    linarith
  have hmodel := hC (P.a c) (P.κ c) (chartZeta P c z') ha_ne hκK hζpos hζ4 h4a hslit
  have hmodel' : ‖Work.Implosion.approxEcal (P.a c) (P.κ c)
        (Work.Implosion.ecalCoord (P.a c) (chartZeta P c z'))
      - ((chartZeta P c z')⁻¹ - P.κ c * Complex.log (chartZeta P c z'))‖ ≤
      C * ‖P.a c‖ ^ 2 / ‖chartZeta P c z'‖ ^ 3 := by
    simpa only [one_div] using hmodel
  have hsize : C * ‖P.a c‖ ^ 2 / ‖chartZeta P c z'‖ ^ 3 ≤ ε / 2 := by
    rw [hanorm]
    have hζlo : reLo ≤ ‖chartZeta P c z'‖ := le_trans hζre (Complex.re_le_norm _)
    have hζ3pos : 0 < ‖chartZeta P c z'‖ ^ 3 := by
      have h : 0 < ‖chartZeta P c z'‖ := lt_of_lt_of_le hreLo hζlo
      positivity
    have h1 : C * (P.lam c) ^ 2 ≤ C * lamMax ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlam_pos.le hlamle 2) hC0
    have h2 : reLo ^ 3 ≤ ‖chartZeta P c z'‖ ^ 3 := pow_le_pow_left₀ hreLo.le hζlo 3
    have h4 : C * (P.lam c) ^ 2 ≤ (ε / 2) * reLo ^ 3 := by
      have h5 := hmodel_bound
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < reLo ^ 3)] at h5
      linarith
    rw [div_le_iff₀ hζ3pos]
    have h3 : (ε / 2) * reLo ^ 3 ≤ (ε / 2) * ‖chartZeta P c z'‖ ^ 3 :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have hΓz₀ : (zeta0 P z)⁻¹ - P.κ c₀ * Complex.log (zeta0 P z)
      = -Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P z) := by
    have h1 := w0_eq_neg_inv_zeta0 P hz.1
    have hζ₀inv : (zeta0 P z)⁻¹ = -(Work.PARIMPL2.w0 P z) := by rw [h1]; ring
    have harg : (-(Work.PARIMPL2.w0 P z)).arg ≠ Real.pi := by
      intro hcon
      have hpos : 0 < (-(Work.PARIMPL2.w0 P z)).re := by
        rw [Complex.neg_re]
        linarith [hz.2.1.2]
      have hlt : |(-(Work.PARIMPL2.w0 P z)).arg| < Real.pi / 2 :=
        Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpos)
      rw [hcon, abs_of_pos Real.pi_pos] at hlt
      linarith [Real.pi_pos]
    have hζ₀eq : zeta0 P z = (-(Work.PARIMPL2.w0 P z))⁻¹ := by rw [← hζ₀inv, inv_inv]
    have hlog : Complex.log (zeta0 P z) = -Complex.log (-(Work.PARIMPL2.w0 P z)) := by
      rw [hζ₀eq]
      exact Complex.log_inv _ harg
    rw [hζ₀inv, hlog, Work.PARIMPL2.approxCoordRep]
    ring
  have hΓclose : ‖(chartZeta P c z')⁻¹ - P.κ c * Complex.log (chartZeta P c z')
      - ((zeta0 P z)⁻¹ - P.κ c₀ * Complex.log (zeta0 P z))‖ < ε / 2 := by
    have hre₀ : reLo ≤ (zeta0 P z).re := by linarith [hζ₀re2]
    have hnorm₀ : ‖zeta0 P z‖ ≤ 1 / 4 := by linarith [hζ₀norm]
    have hκ1 : ‖P.κ c - P.κ c₀‖ ≤ 1 := le_trans (hκρ c hcκ) (min_le_right _ _)
    have hκδ : ‖P.κ c - P.κ c₀‖ ≤ d1 / 2 := le_trans (hκρ c hcκ) (min_le_left _ _)
    have hd : dist (((chartZeta P c z'), P.κ c) : ℂ × ℂ) (((zeta0 P z), P.κ c₀) : ℂ × ℂ) < d1 := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [dist_eq_norm]
        linarith [hζclose, hD₁, hd1pos]
      · rw [dist_eq_norm]
        linarith [hd1pos]
    have h := hunif (chartZeta P c z', P.κ c) (zeta0 P z, P.κ c₀)
      hζre hζnorm hre₀ hnorm₀ hκ1 (by simp) hd
    simpa [dist_eq_norm] using h
  have hsplit : Work.PARIMPL.approxU P c z'
      + Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P z)
      = (Work.Implosion.approxEcal (P.a c) (P.κ c) (Work.Implosion.ecalCoord (P.a c) (chartZeta P c z'))
          - ((chartZeta P c z')⁻¹ - P.κ c * Complex.log (chartZeta P c z')))
        + (((chartZeta P c z')⁻¹ - P.κ c * Complex.log (chartZeta P c z'))
          - ((zeta0 P z)⁻¹ - P.κ c₀ * Complex.log (zeta0 P z))) := by
    rw [hΓz₀, Work.PARIMPL.approxU, Work.PARIMPL.ecalU]
    ring
  calc ‖Work.PARIMPL.approxU P c z'
        + Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P z)‖
      = ‖(Work.Implosion.approxEcal (P.a c) (P.κ c)
            (Work.Implosion.ecalCoord (P.a c) (chartZeta P c z'))
          - ((chartZeta P c z')⁻¹ - P.κ c * Complex.log (chartZeta P c z')))
        + (((chartZeta P c z')⁻¹ - P.κ c * Complex.log (chartZeta P c z'))
          - ((zeta0 P z)⁻¹ - P.κ c₀ * Complex.log (zeta0 P z)))‖ := by rw [hsplit]
    _ ≤ ‖Work.Implosion.approxEcal (P.a c) (P.κ c) (Work.Implosion.ecalCoord (P.a c) (chartZeta P c z'))
          - ((chartZeta P c z')⁻¹ - P.κ c * Complex.log (chartZeta P c z'))‖
        + ‖((chartZeta P c z')⁻¹ - P.κ c * Complex.log (chartZeta P c z'))
          - ((zeta0 P z)⁻¹ - P.κ c₀ * Complex.log (zeta0 P z))‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (le_trans hmodel' hsize) (le_of_lt hΓclose)
    _ = ε := by ring

end Work.PARIMPL2.Lavaurs
