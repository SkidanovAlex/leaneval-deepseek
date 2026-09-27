import Mathlib
import Submission.Work.Drive.DirCTools
import Submission.Work.Measurable

namespace Work.Drive

open Filter Set
open Manifold Topology
open scoped Manifold ContDiff Topology

open Submission.Collision (dirC)

/-- **Secant slopes of a `C¹` curve tend to the tangent.** If `G : ℝ → ℝ × ℝ` is `C¹` and
`s n ≠ t n`, `s n, t n → x`, then the secant slope `(s n - t n)⁻¹ • (G (s n) - G (t n))` tends to
`deriv G x`. -/
theorem tendsto_secant_slope (G : ℝ → ℝ × ℝ) (hG : ContDiff ℝ 1 G) (x : ℝ)
    {s t : ℕ → ℝ} (hs : Filter.Tendsto s Filter.atTop (𝓝 x))
    (ht : Filter.Tendsto t Filter.atTop (𝓝 x)) (hst : ∀ n, s n ≠ t n) :
    Filter.Tendsto (fun n => (s n - t n)⁻¹ • (G (s n) - G (t n))) Filter.atTop
      (𝓝 (deriv G x)) := by
  set L : ℝ × ℝ := deriv G x with hL
  set H : ℝ → ℝ × ℝ := fun y => G y - (y - x) • L with hH
  have hGdiff : ∀ y, DifferentiableAt ℝ G y := fun y => hG.differentiable_one.differentiableAt
  have hd1 : ∀ y, HasDerivAt (fun z : ℝ => (z - x) • L) L y := by
    intro y
    have h := ((hasDerivAt_id y).sub_const x).smul_const L
    simpa using h
  have hHderiv_at : ∀ y, HasDerivAt H (deriv G y - L) y := by
    intro y
    rw [hH]
    exact ((hGdiff y).hasDerivAt).sub (hd1 y)
  have hHderiv : ∀ y, deriv H y = deriv G y - L := fun y => (hHderiv_at y).deriv
  have hHdiff : ∀ y, DifferentiableAt ℝ H y := fun y => (hHderiv_at y).differentiableAt
  have hdHcont : Continuous (deriv H) := by
    rw [show deriv H = fun y => deriv G y - L from funext hHderiv]
    exact hG.continuous_deriv_one.sub continuous_const
  have hdHx : deriv H x = 0 := by rw [hHderiv x, hL, sub_self]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hev : ∀ᶠ y in 𝓝 x, ‖deriv H y‖ < ε / 2 := by
    have ht0 : Filter.Tendsto (deriv H) (𝓝 x) (𝓝 0) := by
      rw [← hdHx]; exact hdHcont.continuousAt
    simpa using (Metric.tendsto_nhds.mp ht0) (ε / 2) hε2
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  have hs_ev : ∀ᶠ n in atTop, |s n - x| < δ := by
    have h := (Metric.tendsto_nhds.mp hs) δ hδpos
    simpa [Real.dist_eq] using h
  have ht_ev : ∀ᶠ n in atTop, |t n - x| < δ := by
    have h := (Metric.tendsto_nhds.mp ht) δ hδpos
    simpa [Real.dist_eq] using h
  rw [Filter.eventually_atTop] at hs_ev ht_ev
  obtain ⟨N1, hN1⟩ := hs_ev
  obtain ⟨N2, hN2⟩ := ht_ev
  refine ⟨max N1 N2, ?_⟩
  intro n hn
  have hsx : |s n - x| < δ := hN1 n (le_trans (le_max_left _ _) hn)
  have htx : |t n - x| < δ := hN2 n (le_trans (le_max_right _ _) hn)
  have hne : s n - t n ≠ 0 := sub_ne_zero.mpr (hst n)
  have hsδ1 : x - δ < s n := by have := (abs_lt.mp hsx).1; linarith
  have hsδ2 : s n < x + δ := by have := (abs_lt.mp hsx).2; linarith
  have htδ1 : x - δ < t n := by have := (abs_lt.mp htx).1; linarith
  have htδ2 : t n < x + δ := by have := (abs_lt.mp htx).2; linarith
  have hbound : ‖H (s n) - H (t n)‖ ≤ ε / 2 * ‖s n - t n‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.Icc (min (s n) (t n)) (max (s n) (t n))) (C := ε / 2)
      (x := t n) (y := s n) ?_ ?_ (convex_Icc _ _) ?_ ?_
    · intro y _
      exact hHdiff y
    · intro y hy
      rw [Set.mem_Icc] at hy
      have hyδ : |y - x| < δ := by
        rw [abs_lt]
        constructor
        · have h1 : x - δ < min (s n) (t n) := lt_min hsδ1 htδ1
          linarith [hy.1]
        · have h2 : max (s n) (t n) < x + δ := max_lt hsδ2 htδ2
          linarith [hy.2]
      exact le_of_lt (hδ (by rw [Real.dist_eq]; exact hyδ))
    · exact ⟨min_le_right _ _, le_max_right _ _⟩
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
  have hbound' : ‖H (s n) - H (t n)‖ ≤ ε / 2 * |s n - t n| := by
    simpa [Real.norm_eq_abs] using hbound
  have hHsub : H (s n) - H (t n) = (G (s n) - G (t n)) - (s n - t n) • L := by
    rw [hH]
    simp only
    rw [sub_smul]
    module
  have hkey : (s n - t n)⁻¹ • (G (s n) - G (t n)) - L
      = (s n - t n)⁻¹ • (H (s n) - H (t n)) := by
    rw [← inv_smul_smul₀ hne L, ← smul_sub, ← hHsub]
  have hpos : 0 < |s n - t n| := abs_pos.mpr hne
  rw [dist_eq_norm, hkey, norm_smul, Real.norm_eq_abs, abs_inv]
  calc |s n - t n|⁻¹ * ‖H (s n) - H (t n)‖
      ≤ |s n - t n|⁻¹ * (ε / 2 * |s n - t n|) :=
        mul_le_mul_of_nonneg_left hbound' (by positivity)
    _ = ε / 2 := by
        rw [mul_comm (ε / 2) |s n - t n|, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
    _ < ε := by linarith

/-- **The chord direction of a `C¹` curve tends to the tangent direction.**

If `G : ℝ → ℝ × ℝ` is `C¹`, `deriv G x ≠ 0`, and `s n ≠ t n` with `s n, t n → x`, then the doubled
direction (`Submission.Collision.dirC`, the class of `arg/π` in `ℝ/ℤ`, insensitive to nonzero real
scaling: `Submission.Work.Drive.dirC_smul_ne`) of the chord `G (s n) - G (t n)` tends to the doubled
direction of the tangent `deriv G x`.-/
theorem secant_dirC_limit {G : ℝ → ℝ × ℝ} (hG : ContDiff ℝ 1 G) {x : ℝ}
    (hne : deriv G x ≠ 0) {s t : ℕ → ℝ} (hs : Filter.Tendsto s Filter.atTop (𝓝 x))
    (ht : Filter.Tendsto t Filter.atTop (𝓝 x)) (hst : ∀ n, s n ≠ t n) :
    Filter.Tendsto (fun n => Submission.Collision.dirC (G (s n) - G (t n))) Filter.atTop
      (𝓝 (Submission.Collision.dirC (deriv G x))) := by
  have hslope : Filter.Tendsto (fun n => (s n - t n)⁻¹ • (G (s n) - G (t n))) Filter.atTop
      (𝓝 (deriv G x)) := tendsto_secant_slope G hG x hs ht hst
  have hcont : ContinuousAt dirC (deriv G x) :=
    Submission.Configuration.continuousOn_dirC.continuousAt
      ((isOpen_ne (x := (0 : ℝ × ℝ))).mem_nhds hne)
  have hcomp : Filter.Tendsto (fun n => dirC ((s n - t n)⁻¹ • (G (s n) - G (t n)))) Filter.atTop
      (𝓝 (dirC (deriv G x))) := hcont.tendsto.comp hslope
  refine hcomp.congr' ?_
  filter_upwards with n
  exact dirC_smul_ne (inv_ne_zero (sub_ne_zero.mpr (hst n))) (G (s n) - G (t n))

end Work.Drive
