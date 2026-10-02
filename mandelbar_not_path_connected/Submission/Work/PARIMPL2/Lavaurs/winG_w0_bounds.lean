import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000

open Classical
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

/-- **Elementary geometry of the incoming window in the `c₀`-chart.**  For `R ≥ 8 (H+1)` and
`z ∈ WinG P R H` (i.e. `z ≠ d.z₁`, `Re (w0 P z) ∈ [R, R+2]`, `|Im (w0 P z)| ≤ H`, where
`w0 P z = −P.s c₀/(z − d.z₁)`):

* `0 ≤ H` and `8 ≤ R` (the window is empty for `H < 0`);
* `w0 P z ≠ 0` and `(z − d.z₁) * w0 P z = −P.s c₀`, hence `‖z − d.z₁‖ = ‖P.s c₀‖ / ‖w0 P z‖`;
* `R ≤ ‖w0 P z‖ ≤ R + 2 + H`;
* the `c₀`-chart coordinate `ζ₀ = chartZeta P c₀ z = (z − d.z₁)/P.s c₀` satisfies
  `ζ₀ = −1/w0 P z`, `‖ζ₀‖ ≤ 1/R` and `Re ζ₀ ≤ −R/(R+2+H)²` (so `ζ₀` is not small in the sense
  `|Re ζ₀| ≥ R/(R+2+H)² > 0`);
* `‖log (w0 P z)‖ ≤ Real.log (R + 2 + H) + Real.pi`. -/
theorem winG_w0_bounds {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) {R H : ℝ} (hH : R ≥ 8 * (H + 1))
    {z : ℂ} (hz : z ∈ Work.PARIMPL2.WinG P R H) :
    0 ≤ H ∧ 8 ≤ R ∧ Work.PARIMPL2.w0 P z ≠ 0 ∧
      (z - d.z₁) * Work.PARIMPL2.w0 P z = -P.s c₀ ∧
      R ≤ ‖Work.PARIMPL2.w0 P z‖ ∧ ‖Work.PARIMPL2.w0 P z‖ ≤ R + 2 + H ∧
      Work.PARIMPL.chartZeta P c₀ z = -1 / Work.PARIMPL2.w0 P z ∧
      ‖Work.PARIMPL.chartZeta P c₀ z‖ ≤ 1 / R ∧
      (Work.PARIMPL.chartZeta P c₀ z).re ≤ -(R / (R + 2 + H) ^ 2) ∧
      ‖Complex.log (Work.PARIMPL2.w0 P z)‖ ≤ Real.log (R + 2 + H) + Real.pi := by
  simp only [Work.PARIMPL2.WinG, Set.mem_ofPred_eq] at hz
  obtain ⟨hz1, hzre, hzim⟩ := hz
  obtain ⟨hzR, hzR2⟩ := hzre
  -- the window is empty for `H < 0`, and `R ≥ 8 (H+1) ≥ 8`
  have hHnn : 0 ≤ H := le_trans (abs_nonneg _) hzim
  have hR8 : 8 ≤ R := by nlinarith [hH]
  have hRpos : 0 < R := by linarith
  have hre_pos : 0 < (Work.PARIMPL2.w0 P z).re := by linarith
  have hwne : Work.PARIMPL2.w0 P z ≠ 0 := by
    intro h
    rw [h] at hzR
    simp at hzR
    linarith
  have hz_ne : z - d.z₁ ≠ 0 := sub_ne_zero.mpr hz1
  have hs0 : P.s c₀ ≠ 0 := P.s_ne c₀ (Metric.mem_ball_self P.hρ₀)
  -- the defining product relation of `w₀`
  have hprod : (z - d.z₁) * Work.PARIMPL2.w0 P z = -P.s c₀ := by
    rw [Work.PARIMPL2.w0]
    field_simp
  -- the modulus bounds
  have hw_lower : R ≤ ‖Work.PARIMPL2.w0 P z‖ := le_trans hzR (Complex.re_le_norm _)
  have hw_upper : ‖Work.PARIMPL2.w0 P z‖ ≤ R + 2 + H := by
    have h1 : |(Work.PARIMPL2.w0 P z).re| ≤ R + 2 := by
      rw [abs_of_nonneg (le_of_lt hre_pos)]
      exact hzR2
    have h2 := Complex.norm_le_abs_re_add_abs_im (Work.PARIMPL2.w0 P z)
    linarith
  -- the chart coordinate `ζ₀ = -1/w₀`
  have hmul : Work.PARIMPL.chartZeta P c₀ z * Work.PARIMPL2.w0 P z = -1 := by
    rw [Work.PARIMPL.chartZeta, P.m₀, Work.PARIMPL2.w0]
    field_simp
  have hzeta_eq : Work.PARIMPL.chartZeta P c₀ z = -1 / Work.PARIMPL2.w0 P z :=
    (eq_div_iff_mul_eq hwne).mpr hmul
  have hzeta_norm : ‖Work.PARIMPL.chartZeta P c₀ z‖ ≤ 1 / R := by
    rw [hzeta_eq, show (-1 : ℂ) / Work.PARIMPL2.w0 P z
        = -(1 / Work.PARIMPL2.w0 P z) from by ring]
    rw [norm_neg, norm_div, norm_one]
    exact one_div_le_one_div_of_le hRpos hw_lower
  have hzeta_re : (Work.PARIMPL.chartZeta P c₀ z).re ≤ -(R / (R + 2 + H) ^ 2) := by
    have hnormSq_pos : 0 < Complex.normSq (Work.PARIMPL2.w0 P z) :=
      Complex.normSq_pos.mpr hwne
    have hnormSq_le : Complex.normSq (Work.PARIMPL2.w0 P z) ≤ (R + 2 + H) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [hw_upper, norm_nonneg (Work.PARIMPL2.w0 P z)]
    have key : R / (R + 2 + H) ^ 2 ≤
        (Work.PARIMPL2.w0 P z).re / Complex.normSq (Work.PARIMPL2.w0 P z) := by
      have h1 : R / (R + 2 + H) ^ 2 ≤ R / Complex.normSq (Work.PARIMPL2.w0 P z) :=
        div_le_div_of_nonneg_left hRpos.le hnormSq_pos hnormSq_le
      have h2 : R / Complex.normSq (Work.PARIMPL2.w0 P z) ≤
          (Work.PARIMPL2.w0 P z).re / Complex.normSq (Work.PARIMPL2.w0 P z) :=
        div_le_div_of_nonneg_right hzR hnormSq_pos.le
      linarith
    rw [hzeta_eq, show (-1 : ℂ) / Work.PARIMPL2.w0 P z
        = -(1 / Work.PARIMPL2.w0 P z) from by ring]
    rw [Complex.neg_re, one_div, Complex.inv_re]
    linarith
  -- the logarithm bound
  have hlog : ‖Complex.log (Work.PARIMPL2.w0 P z)‖ ≤ Real.log (R + 2 + H) + Real.pi := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (Complex.log (Work.PARIMPL2.w0 P z))
    rw [Complex.log_re, Complex.log_im] at h1
    have hge1 : (1 : ℝ) ≤ ‖Work.PARIMPL2.w0 P z‖ := by linarith
    have hpos : 0 < ‖Work.PARIMPL2.w0 P z‖ := by linarith
    have h2 : |Real.log ‖Work.PARIMPL2.w0 P z‖| ≤ Real.log (R + 2 + H) := by
      rw [abs_of_nonneg (Real.log_nonneg hge1)]
      exact Real.log_le_log hpos hw_upper
    have h3 : |(Work.PARIMPL2.w0 P z).arg| ≤ Real.pi :=
      abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
    linarith
  exact ⟨hHnn, hR8, hwne, hprod, hw_lower, hw_upper, hzeta_eq, hzeta_norm, hzeta_re, hlog⟩

end Work.PARIMPL2.Lavaurs
