import Mathlib
import Submission.Work.Pert.Setup

set_option linter.unusedVariables false

namespace Work.Pert

open MandelDim Complex Set Metric

noncomputable section

/-!
# PERT · the horizontal slices of the gate `Qm`

`Qm ξ α = Qreg (some (ξ - 1/α)) (some (-ξ))` is the complement of two closed 90° cones with apices
`b₁ = ξ - 1/α` and `b₂ = -ξ`.  Writing `x = Re z`, `t = Im z`, membership is the pair of *linear*
inequalities

* (A-cone at `b₁`)  `ξ - (1/α).re - |t + (1/α).im| < x`,
* (B-cone at `b₂`)  `x < |t| - ξ`,

so the slice `Qm ξ α ∩ {Im = t}` is the open interval `(lo t, hi t)`.  The distance from a point of
the slice to the complement of the gate is at least `min (x - lo t) (hi t - x) / √2` (the two cone
boundaries are 45° lines).

These are the quantitative facts the strip argument uses.
-/

lemma sqrt2_norm (v : ℂ) : (|v.re| + |v.im|) ≤ Real.sqrt 2 * ‖v‖ := by
  have h2 : (|v.re| + |v.im|)^2 ≤ (Real.sqrt 2 * ‖v‖)^2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have hnorm : ‖v‖^2 = v.re^2 + v.im^2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have ham := sq_nonneg (|v.re| - |v.im| : ℝ)
    rw [sub_sq, sq_abs, sq_abs] at ham
    rw [add_sq, sq_abs, sq_abs, hnorm]
    linarith
  have h3 : (0:ℝ) ≤ |v.re| + |v.im| := by positivity
  have h4 : (0:ℝ) ≤ Real.sqrt 2 * ‖v‖ := by positivity
  nlinarith [h2, h3, h4]

lemma abs_re_sub_im (z : ℂ) : |z.re - z.im| ≤ |z.re| + |z.im| := by
  have h' : |z.re + -(z.im)| ≤ |z.re| + |-(z.im)| := abs_add_le _ _
  rw [abs_neg] at h'
  simpa [sub_eq_add_neg] using h'

/-- Points of the closed cone `{v | v.re + |v.im| ≤ 0}` (apex `0`, opening left) are at distance at
least `(p.re + |p.im|)/√2` from `p`. -/
lemma le_norm_of_leftCone {p v : ℂ} (hv : v.re + |v.im| ≤ 0) :
    (p.re + |p.im|) / Real.sqrt 2 ≤ ‖p - v‖ := by
  have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rcases le_total 0 p.im with hp | hp
  · rw [abs_of_nonneg hp]
    have h1 : p.re + p.im ≤ (p - v).re + (p - v).im := by
      have hv' : v.re + v.im ≤ 0 := by linarith [le_abs_self v.im]
      simp only [Complex.sub_re, Complex.sub_im]; linarith
    have h2 : |(p - v).re + (p - v).im| ≤ |(p-v).re| + |(p-v).im| := abs_add_le _ _
    have h3 : |(p-v).re| + |(p-v).im| ≤ Real.sqrt 2 * ‖p - v‖ := sqrt2_norm _
    have h0 : (p - v).re + (p - v).im ≤ |(p - v).re + (p - v).im| := le_abs_self _
    rw [div_le_iff₀ hs]
    linarith
  · rw [abs_of_nonpos hp]
    have h1 : p.re - p.im ≤ (p - v).re - (p - v).im := by
      have hv' : v.re - v.im ≤ 0 := by linarith [neg_abs_le v.im]
      simp only [Complex.sub_re, Complex.sub_im]; linarith
    have h2 : |(p - v).re - (p - v).im| ≤ |(p-v).re| + |(p-v).im| := abs_re_sub_im _
    have h3 : |(p-v).re| + |(p-v).im| ≤ Real.sqrt 2 * ‖p - v‖ := sqrt2_norm _
    have h0 : (p - v).re - (p - v).im ≤ |(p - v).re - (p - v).im| := le_abs_self _
    rw [div_le_iff₀ hs]
    linarith

/-- Points of the closed cone `{v | |v.im| ≤ v.re}` (apex `0`, opening right) are at distance at
least `(|q.im| - q.re)/√2` from `q`. -/
lemma le_norm_of_rightCone {q v : ℂ} (hv : |v.im| ≤ v.re) :
    (|q.im| - q.re) / Real.sqrt 2 ≤ ‖q - v‖ := by
  have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rcases le_total 0 q.im with hq | hq
  · rw [abs_of_nonneg hq]
    have hv' : 0 ≤ v.re - v.im := by linarith [(abs_le.mp hv).2]
    have h1 : (q - v).re - (q - v).im ≤ -(q.im - q.re) := by
      simp only [Complex.sub_re, Complex.sub_im]; linarith
    have h2 : q.im - q.re ≤ |(q - v).re - (q - v).im| := by
      have := neg_le_abs ((q - v).re - (q - v).im); linarith
    have h3 : |(q - v).re - (q - v).im| ≤ |(q-v).re| + |(q-v).im| := abs_re_sub_im _
    have h4 : |(q-v).re| + |(q-v).im| ≤ Real.sqrt 2 * ‖q - v‖ := sqrt2_norm _
    rw [div_le_iff₀ hs]
    linarith
  · rw [abs_of_nonpos hq]
    have hv' : 0 ≤ v.re + v.im := by linarith [(abs_le.mp hv).1]
    have h1 : (q - v).re + (q - v).im ≤ -(-q.im - q.re) := by
      simp only [Complex.sub_re, Complex.sub_im]; linarith
    have h2 : -q.im - q.re ≤ |(q - v).re + (q - v).im| := by
      have := neg_le_abs ((q - v).re + (q - v).im); linarith
    have h3 : |(q - v).re + (q - v).im| ≤ |(q-v).re| + |(q-v).im| := abs_add_le _ _
    have h4 : |(q-v).re| + |(q-v).im| ≤ Real.sqrt 2 * ‖q - v‖ := sqrt2_norm _
    rw [div_le_iff₀ hs]
    linarith

theorem Qm_mem_iff {ξ : ℝ} {α z : ℂ} :
    z ∈ Qm ξ α ↔ (ξ - (1/α).re - |z.im + (1/α).im| < z.re ∧ z.re < |z.im| - ξ) := by
  unfold Qm MandelDim.Qreg
  constructor
  · rintro ⟨hA, hB⟩
    have hA2 : -|z.im + (1/α).im| < z.re - (ξ - (1/α).re) := by
      have h := hA ((ξ:ℂ) - 1/α) (by simp)
      simpa [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] using h
    have hB2 : z.re + ξ < |z.im| := by
      have h := hB (-(ξ:ℂ)) (by simp)
      simpa [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] using h
    constructor <;> linarith
  · rintro ⟨hA, hB⟩
    refine ⟨?_, ?_⟩
    · intro b hb
      rw [Option.mem_def, Option.some.injEq] at hb
      subst hb
      have h : -|z.im + (1/α).im| < z.re - (ξ - (1/α).re) := by linarith
      simpa [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] using h
    · intro b hb
      rw [Option.mem_def, Option.some.injEq] at hb
      subst hb
      have h : z.re + ξ < |z.im| := by linarith
      simpa [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im] using h

theorem Qm_mem_iff' {ξ t x : ℝ} {α : ℂ} :
    (x + t * Complex.I : ℂ) ∈ Qm ξ α ↔
      (ξ - (1 / α).re - |t + (1 / α).im| < x ∧ x < |t| - ξ) := by
  rw [Qm_mem_iff]
  have h1 : (x + t * Complex.I : ℂ).re = x := by simp
  have h2 : (x + t * Complex.I : ℂ).im = t := by simp
  rw [h1, h2]

/-- The two endpoints of the gate slice at height `t`. -/
def sliceLo (ξ : ℝ) (α : ℂ) (t : ℝ) : ℝ := ξ - (1/α).re - |t + (1/α).im|
def sliceHi (ξ : ℝ) (t : ℝ) : ℝ := |t| - ξ

theorem Qm_sep {ξ x t : ℝ} {α : ℂ} (h : (x + t * Complex.I : ℂ) ∈ Qm ξ α) :
    ∀ u : ℂ, u ∉ Work.Pert.Qm ξ α →
      min (x - sliceLo ξ α t) (sliceHi ξ t - x) / Real.sqrt 2 ≤
        dist (x + t * Complex.I : ℂ) u := by
  intro u hu
  rw [Qm_mem_iff] at hu
  simp only [not_and_or, not_lt] at hu
  rcases hu with hu | hu
  · -- `u` is in the closed A-cone (apex `b₁ = ξ - 1/α`)
    have hv : (u - ((ξ:ℂ) - 1/α)).re + |(u - ((ξ:ℂ) - 1/α)).im| ≤ 0 := by
      have h1 : (u - ((ξ:ℂ) - 1/α)).re = u.re - ξ + (1/α).re := by
        simp only [Complex.sub_re, Complex.ofReal_re]
        ring
      have h2 : (u - ((ξ:ℂ) - 1/α)).im = u.im + (1/α).im := by
        simp only [Complex.sub_im, Complex.ofReal_im]
        ring
      rw [h1, h2]; linarith
    have key := le_norm_of_leftCone (p := (x + t * Complex.I : ℂ) - ((ξ:ℂ) - 1/α)) (v := u - ((ξ:ℂ) - 1/α)) hv
    have hp : ((x + t * Complex.I : ℂ) - ((ξ:ℂ) - 1/α)).re +
        |((x + t * Complex.I : ℂ) - ((ξ:ℂ) - 1/α)).im| = x - sliceLo ξ α t := by
      simp only [sliceLo, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, add_zero, sub_zero]
      ring
    have hsub : ((x + t * Complex.I : ℂ) - ((ξ:ℂ) - 1/α)) - (u - ((ξ:ℂ) - 1/α)) =
        (x + t * Complex.I : ℂ) - u := by ring
    rw [hp] at key
    rw [hsub] at key
    have hdist : dist (x + t * Complex.I : ℂ) u = ‖(x + t * Complex.I : ℂ) - u‖ := dist_eq_norm _ _
    rw [hdist]
    exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg 2)) key
  · -- `u` is in the closed B-cone (apex `b₂ = -ξ`)
    have hv : |(u - (-(ξ:ℂ))).im| ≤ (u - (-(ξ:ℂ))).re := by
      have h1 : (u - (-(ξ:ℂ))).re = u.re + ξ := by
        simp [Complex.sub_re, Complex.ofReal_re]
      have h2 : (u - (-(ξ:ℂ))).im = u.im := by
        simp [Complex.sub_im, Complex.ofReal_im]
      rw [h1, h2]; linarith
    have key := le_norm_of_rightCone (q := (x + t * Complex.I : ℂ) - (-(ξ:ℂ))) (v := u - (-(ξ:ℂ))) hv
    have hq : |((x + t * Complex.I : ℂ) - (-(ξ:ℂ))).im| - ((x + t * Complex.I : ℂ) - (-(ξ:ℂ))).re
        = sliceHi ξ t - x := by
      simp only [sliceHi, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, sub_zero]
      ring
    have hsub : ((x + t * Complex.I : ℂ) - (-(ξ:ℂ))) - (u - (-(ξ:ℂ))) =
        (x + t * Complex.I : ℂ) - u := by ring
    rw [hq] at key
    rw [hsub] at key
    have hdist : dist (x + t * Complex.I : ℂ) u = ‖(x + t * Complex.I : ℂ) - u‖ := dist_eq_norm _ _
    rw [hdist]
    exact le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg 2)) key

theorem ball_subset_Qm_of_margin_slice {ξ x t r : ℝ} {α : ℂ}
    (h : (x + t * Complex.I : ℂ) ∈ Qm ξ α)
    (hr : r * Real.sqrt 2 ≤ min (x - sliceLo ξ α t) (sliceHi ξ t - x)) :
    Metric.ball (x + t * Complex.I : ℂ) r ⊆ Work.Pert.Qm ξ α := by
  have hs : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  intro u hu
  by_contra huc
  have hkey := Qm_sep h u huc
  rw [Metric.mem_ball, dist_comm] at hu
  have h1 : r * Real.sqrt 2 ≤ min (x - sliceLo ξ α t) (sliceHi ξ t - x) := hr
  have h2 : min (x - sliceLo ξ α t) (sliceHi ξ t - x) ≤ dist (x + t * Complex.I : ℂ) u * Real.sqrt 2 := by
    have := mul_le_mul_of_nonneg_right hkey hs.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hs)] at this
  have h3 : r ≤ dist (x + t * Complex.I : ℂ) u := by
    have h4 := le_trans h1 h2
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith [h4, hs, hs2, dist_nonneg (x := (x + t * Complex.I : ℂ)) (y := u)]
  linarith

end

end Work.Pert
