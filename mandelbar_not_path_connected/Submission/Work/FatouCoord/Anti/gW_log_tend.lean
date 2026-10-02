import Mathlib
import Submission.Work.FatouCoord.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Anti

open Filter Set Metric
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- Branch of the principal logarithm: if `b` and `a / b` both lie in the open right
half-plane, then `arg (a / b) + arg b ∈ (-π, π]` and the logarithm splits. -/
lemma log_eq_log_div_add_log {a b : ℂ} (hb : 0 < b.re) (hab : 0 < (a / b).re) :
    Complex.log a = Complex.log (a / b) + Complex.log b := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hx0 : a / b ≠ 0 := by rintro h; rw [h] at hab; simp at hab
  have hargx : |(a / b).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hab)
  have hargb : |b.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have hsum : (a / b).arg + b.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Set.mem_Ioc]
    obtain ⟨hx1, hx2⟩ := abs_lt.mp hargx
    obtain ⟨hb1, hb2⟩ := abs_lt.mp hargb
    exact ⟨by linarith, by linarith⟩
  have h := Complex.log_mul (x := a / b) (y := b) hx0 hb0 hsum
  rwa [div_mul_cancel₀ a hb0] at h

lemma log_sub_log_eq_log_div {a b : ℂ} (hb : 0 < b.re) (hab : 0 < (a / b).re) :
    Complex.log a - Complex.log b = Complex.log (a / b) := by
  rw [log_eq_log_div_add_log hb hab]; ring

lemma star_chart (w : ℂ) : star (Work.FatouCoord.chart w) = -1 / star w := by
  simp [Work.FatouCoord.chart]

/-- The chart conjugate of an anti-holomorphic germ differs from `star w` by
`(g u - star u) / (g u * star u)` where `u = chart w`. -/
lemma chart_sub_star_eq {g : ℂ → ℂ} {w : ℂ} (hw : w ≠ 0)
    (hg : g (Work.FatouCoord.chart w) ≠ 0) (hu : star (Work.FatouCoord.chart w) ≠ 0) :
    Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) - star w =
      (g (Work.FatouCoord.chart w) - star (Work.FatouCoord.chart w)) /
        (g (Work.FatouCoord.chart w) * star (Work.FatouCoord.chart w)) := by
  have hstar : star w = -1 / star (Work.FatouCoord.chart w) := by
    rw [star_chart w]
    field_simp
  rw [hstar, Work.FatouCoord.chart]
  field_simp
  ring

theorem gW_log_tend {g : ℂ → ℂ} {r G : ℝ} {b : ℂ} (hr : 0 < r)
    (hg_lin : ∀ z ∈ Metric.ball 0 r, ‖g z - star z‖ ≤ G * ‖z‖ ^ 2)
    (hb_tend : Filter.Tendsto (fun z : ℂ => (star (g z) - z) / z ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds b)) :
    Filter.Tendsto (fun w : ℂ => Complex.log (Work.FatouCoord.chart (g (Work.FatouCoord.chart w))) - Complex.log (star w))
      (Filter.comap Complex.re Filter.atTop) (nhds 0) := by
  set F : Filter ℂ := Filter.comap Complex.re Filter.atTop with hF
  -- `G` is nonnegative.
  have hG : 0 ≤ G := by
    have hz : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    have hznorm : ‖(((r / 2 : ℝ) : ℂ))‖ = r / 2 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hlin := hg_lin _ hz
    rw [hznorm] at hlin
    have hpos : 0 < (r / 2) ^ 2 := by positivity
    nlinarith [hlin, norm_nonneg (g (((r / 2 : ℝ) : ℂ)) - star (((r / 2 : ℝ) : ℂ))), hpos]
  have hre : Tendsto (fun w : ℂ => Complex.re w) F atTop := by
    rw [hF]; exact Filter.tendsto_comap
  have hnorm : Tendsto (fun w : ℂ => ‖w‖) F atTop := by
    rw [Filter.tendsto_atTop]
    intro a
    filter_upwards [hre.eventually_ge_atTop (max a 0)] with w hw
    exact le_trans (le_max_left a 0) (le_trans hw (Complex.re_le_norm w))
  set M : ℝ := max (1 / r) (4 * G) + 1 with hM
  have hM1 : 1 / r < M := by rw [hM]; linarith [le_max_left (1 / r) (4 * G)]
  have hM2 : 2 * G < M := by
    rw [hM]
    have : (2 : ℝ) * G ≤ 4 * G := by linarith
    linarith [le_max_right (1 / r) (4 * G), this]
  have hM3 : 4 * G < M := by rw [hM]; linarith [le_max_right (1 / r) (4 * G)]
  have hMpos : 0 < M := lt_trans (one_div_pos.mpr hr) hM1
  have hev : ∀ᶠ w in F, M ≤ Complex.re w := hre.eventually_ge_atTop M
  have hbundle : ∀ᶠ w in F,
      ‖Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) - star w‖ ≤ 2 * G ∧
      ‖Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) / star w - 1‖ ≤ 2 * G / ‖w‖ ∧
      (Complex.log (Work.FatouCoord.chart (g (Work.FatouCoord.chart w))) - Complex.log (star w)
        = Complex.log (Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) / star w)) := by
    filter_upwards [hev] with w hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at hw; simp only [Complex.zero_re] at hw; linarith
    have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hw_norm_gt : 1 / r < ‖w‖ :=
      lt_of_lt_of_le hM1 (le_trans hw (Complex.re_le_norm w))
    have hzball : Work.FatouCoord.chart w ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_zero_right, Work.FatouCoord.norm_chart hw0]
      rw [← inv_lt_comm₀ hr hw_norm_pos]
      simpa only [one_div] using hw_norm_gt
    have hlin := hg_lin _ hzball
    have hunorm_pos : 0 < ‖Work.FatouCoord.chart w‖ := by
      rw [Work.FatouCoord.norm_chart hw0]; positivity
    have hGn : G * ‖Work.FatouCoord.chart w‖ ≤ 1 / 2 := by
      rw [Work.FatouCoord.norm_chart hw0, ← div_eq_mul_inv, div_le_iff₀ hw_norm_pos]
      have h2G : 2 * G ≤ ‖w‖ := le_trans (le_of_lt hM2) (le_trans hw (Complex.re_le_norm w))
      linarith
    have hgz_low : ‖Work.FatouCoord.chart w‖ / 2 ≤ ‖g (Work.FatouCoord.chart w)‖ := by
      have h1 : ‖Work.FatouCoord.chart w‖ ≤ ‖g (Work.FatouCoord.chart w)‖ +
          ‖g (Work.FatouCoord.chart w) - star (Work.FatouCoord.chart w)‖ := by
        calc ‖Work.FatouCoord.chart w‖ = ‖star (Work.FatouCoord.chart w)‖ := (norm_star _).symm
          _ = ‖g (Work.FatouCoord.chart w) -
                (g (Work.FatouCoord.chart w) - star (Work.FatouCoord.chart w))‖ :=
                congrArg (fun x : ℂ => ‖x‖) (by ring)
          _ ≤ _ := norm_sub_le _ _
      have h2 : ‖g (Work.FatouCoord.chart w) - star (Work.FatouCoord.chart w)‖ ≤
          (1 / 2) * ‖Work.FatouCoord.chart w‖ := by
        calc ‖g (Work.FatouCoord.chart w) - star (Work.FatouCoord.chart w)‖ ≤
              G * ‖Work.FatouCoord.chart w‖ ^ 2 := hlin
          _ = (G * ‖Work.FatouCoord.chart w‖) * ‖Work.FatouCoord.chart w‖ := by ring
          _ ≤ (1 / 2) * ‖Work.FatouCoord.chart w‖ :=
              mul_le_mul_of_nonneg_right hGn (norm_nonneg _)
      linarith
    have hgu_pos : 0 < ‖g (Work.FatouCoord.chart w)‖ := by linarith
    have hgu_ne : g (Work.FatouCoord.chart w) ≠ 0 := norm_pos_iff.mp hgu_pos
    have hsu_ne : star (Work.FatouCoord.chart w) ≠ 0 := fun h =>
      Work.FatouCoord.chart_ne_zero hw0 (star_eq_zero.mp h)
    have hid := chart_sub_star_eq (g := g) hw0 hgu_ne hsu_ne
    have hbd : ‖Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) - star w‖ ≤ 2 * G := by
      rw [hid, norm_div, norm_mul, norm_star]
      have hnum : ‖g (Work.FatouCoord.chart w) - star (Work.FatouCoord.chart w)‖ ≤
          2 * G * (‖g (Work.FatouCoord.chart w)‖ * ‖Work.FatouCoord.chart w‖) := by
        have hu_le : ‖Work.FatouCoord.chart w‖ ≤ 2 * ‖g (Work.FatouCoord.chart w)‖ := by linarith
        calc ‖g (Work.FatouCoord.chart w) - star (Work.FatouCoord.chart w)‖ ≤
              G * ‖Work.FatouCoord.chart w‖ ^ 2 := hlin
          _ = G * ‖Work.FatouCoord.chart w‖ * ‖Work.FatouCoord.chart w‖ := by ring
          _ ≤ G * ‖Work.FatouCoord.chart w‖ * (2 * ‖g (Work.FatouCoord.chart w)‖) :=
              mul_le_mul_of_nonneg_left hu_le (mul_nonneg hG (norm_nonneg _))
          _ = 2 * G * (‖g (Work.FatouCoord.chart w)‖ * ‖Work.FatouCoord.chart w‖) := by ring
      rw [div_le_iff₀ (mul_pos hgu_pos hunorm_pos)]
      linarith [hnum]
    have hsmall : 2 * G / ‖w‖ < 1 / 2 := by
      rw [div_lt_iff₀ hw_norm_pos]
      have h4 : 4 * G < ‖w‖ := lt_of_lt_of_le hM3 (le_trans hw (Complex.re_le_norm w))
      linarith
    have hsw : star w ≠ 0 := fun h => hw0 (star_eq_zero.mp h)
    have hAdiv : Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) / star w - 1 =
        (Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) - star w) / star w :=
      div_sub_one hsw
    have hAdm : ‖Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) / star w - 1‖ ≤
        2 * G / ‖w‖ := by
      rw [hAdiv, norm_div, norm_star]
      exact div_le_div_of_nonneg_right hbd (norm_nonneg w)
    have hBre : 0 < (star w).re := by
      have : (star w).re = w.re := by simp
      rw [this]; linarith
    have hBr : 0 < (Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) / star w).re := by
      have h1 : -‖Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) / star w - 1‖ ≤
          (Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) / star w - 1).re := by
        have h := Complex.re_le_norm
          (-(Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) / star w - 1))
        rw [Complex.neg_re, norm_neg] at h
        linarith
      have h2 : (Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) / star w).re =
          1 + (Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) / star w - 1).re := by
        rw [Complex.sub_re, Complex.one_re]; ring
      rw [h2]; linarith [h1, hAdm, hsmall]
    exact ⟨hbd, hAdm, log_sub_log_eq_log_div hBre hBr⟩
  have hlim : Tendsto (fun w : ℂ => 2 * G / ‖w‖) F (nhds 0) := by
    have h1 : Tendsto (fun w : ℂ => (‖w‖)⁻¹) F (nhds 0) := hnorm.inv_tendsto_atTop
    have h2 : Tendsto (fun w : ℂ => (2 * G) * (‖w‖)⁻¹) F (nhds 0) := by
      simpa using h1.const_mul (2 * G)
    simpa [div_eq_mul_inv] using h2
  have hAB1 : Tendsto (fun w : ℂ =>
      Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) / star w) F (nhds 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun w => norm_nonneg _) ?_ hlim
    filter_upwards [hbundle] with w hw
    exact hw.2.1
  have hlog0 : Tendsto (fun w : ℂ => Complex.log
      (Work.FatouCoord.chart (g (Work.FatouCoord.chart w)) / star w)) F (nhds 0) := by
    have := hAB1.clog (x := 1) (by rw [Complex.mem_slitPlane_iff]; left; norm_num)
    simpa using this
  refine hlog0.congr' ?_
  filter_upwards [hbundle] with w hw
  exact hw.2.2.symm

end Work.FatouCoord.Anti
