import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# `hptOf` is a right inverse of `yc` at level `D`

In the chart model of `ℍⁿ`, for a boundary point `ξ ∈ Sph n` and a point `u` whose horospherical
level at `ξ` is `D > 0`, the point of the level-`D` horosphere with normalised flat coordinate
`yc ξ u` is `u` itself:

`hptOf ξ (yc ξ u) D = u`.

This is the elementary converse of `hptOf_level`: it says that the parametrisation
`y ↦ hptOf ξ y D` of the horosphere of `ξ` at level `D` is surjective onto that horosphere.

The proof is pure algebra in the chart. Writing `t = tpart u = √(1 + ‖u‖²)` and `c = ⟪u,ξ⟫`,
so that `D = t - c`, `wc ξ u = u - c • ξ` and `yc ξ u = D⁻¹ • (u - c • ξ)`, one computes
`‖wc ξ u‖² = ‖u‖² - c²` (using `‖ξ‖ = 1`), hence
`1 + D²‖yc ξ u‖² = 1 + ‖wc ξ u‖² = t² - c² = D (t + c)`,
so the coefficient of `ξ` in `hptOf ξ (yc ξ u) D` is `(1 + D²‖yc ξ u‖²)/(2D) - D/2 = c`, while
the remaining part `D • yc ξ u` equals `wc ξ u = u - c • ξ`. The two terms reassemble into `u`.
-/

namespace Work.Mostow

open Submission.Mostow

theorem hptOf_yc {n : ℕ} (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (D : ℝ) (hD : 0 < D) (u : Submission.Mostow.E n) (hu : Work.Mostow.lev ξ u = D) :
    Work.Mostow.hptOf ξ (Work.Mostow.yc ξ u) D = u := by
  have hξn : ‖ξ‖ = 1 := by
    simpa [Sph, Metric.mem_sphere, dist_eq_norm] using hξ
  have hξsq : inner ℝ ξ ξ = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hξn]; norm_num
  -- `lev ξ u = tpart u - ⟪u,ξ⟫`, so `hu` is exactly this identity.
  have hlev : tpart u - inner ℝ u ξ = D := hu
  -- `yc ξ u = D⁻¹ • wc ξ u`
  have hyc : yc ξ u = D⁻¹ • wc ξ u := by
    rw [yc, hu]
  -- hence `D • yc ξ u = wc ξ u`
  have hDw : D • yc ξ u = wc ξ u := by
    rw [hyc, smul_smul, mul_inv_cancel₀ (ne_of_gt hD), one_smul]
  -- and `‖wc ξ u‖ = D * ‖yc ξ u‖`
  have hwcn : ‖wc ξ u‖ = D * ‖yc ξ u‖ := by
    rw [← hDw, norm_smul, Real.norm_eq_abs, abs_of_pos hD]
  -- therefore `D ^ 2 * ‖yc ξ u‖ ^ 2 = ‖wc ξ u‖ ^ 2`
  have hD2y : D ^ 2 * ‖yc ξ u‖ ^ 2 = ‖wc ξ u‖ ^ 2 := by
    rw [hwcn, mul_pow]
  -- `‖wc ξ u‖ ^ 2 = ‖u‖ ^ 2 - ⟪u,ξ⟫ ^ 2`
  have hwc_sq : ‖wc ξ u‖ ^ 2 = ‖u‖ ^ 2 - (inner ℝ u ξ) ^ 2 := by
    have h1 : wc ξ u = u - (inner ℝ u ξ) • ξ := rfl
    have h2 : ‖(inner ℝ u ξ) • ξ‖ ^ 2 = (inner ℝ u ξ) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right, hξsq]
      ring
    rw [h1, norm_sub_sq_real, real_inner_smul_right, h2]
    ring
  -- `tpart u ^ 2 = 1 + ‖u‖ ^ 2`
  have ht2 : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := by
    rw [tpart]; exact Real.sq_sqrt (by positivity)
  -- `1 + ‖wc ξ u‖ ^ 2 = D * (tpart u + ⟪u,ξ⟫)`
  have hfac : 1 + ‖wc ξ u‖ ^ 2 = D * (tpart u + inner ℝ u ξ) := by
    have ht : tpart u = D + inner ℝ u ξ := by linarith [hlev]
    rw [hwc_sq]
    have he : (1 : ℝ) + (‖u‖ ^ 2 - (inner ℝ u ξ) ^ 2) = tpart u ^ 2 - (inner ℝ u ξ) ^ 2 := by
      rw [ht2]; ring
    rw [he, ht]; ring
  -- the coefficient of `ξ` in `hptOf ξ (yc ξ u) D` is `⟪u,ξ⟫`
  have hcoe : (1 + D ^ 2 * ‖yc ξ u‖ ^ 2) / (2 * D) - D / 2 = inner ℝ u ξ := by
    rw [hD2y, hfac]
    have ht : tpart u = D + inner ℝ u ξ := by linarith [hlev]
    rw [ht]
    have hDne : D ≠ 0 := ne_of_gt hD
    field_simp
    ring
  show ((1 + D ^ 2 * ‖yc ξ u‖ ^ 2) / (2 * D) - D / 2) • ξ + D • yc ξ u = u
  rw [hcoe, hDw]
  simp only [wc]
  abel

end Work.Mostow
