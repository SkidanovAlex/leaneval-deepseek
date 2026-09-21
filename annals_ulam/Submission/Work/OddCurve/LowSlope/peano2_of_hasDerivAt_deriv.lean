import Mathlib
import Submission.Work.OddCurve.LowSlope.Peano2

/-!
# The Peano second-order expansion from pointwise hypotheses

`Work.OddCurve.LowSlope.Peano2 f x₀ c₁ c₂` records the pointwise (Peano) second order expansion
`f (x₀ + h) = f x₀ + c₁ * h + c₂ / 2 * h ^ 2 + o (h ^ 2)`.

This file proves that it follows from

* `HasDerivAt f c₁ x₀` (the pointwise first derivative), and
* `HasDerivAt (deriv f) c₂ x₀` (the *derivative function* `deriv f` is differentiable at `x₀`),

provided `(c₁, c₂) ≠ (0, 0)`.  The hypothesis `(c₁, c₂) ≠ (0, 0)` is necessary: it is exactly what
rules out the situation where `f` is differentiable *at* `x₀` only.  Indeed `deriv` is total and
equal to `0` at the points where `f` is not differentiable, so

* if `c₁ ≠ 0`, the continuity of `deriv f` at `x₀` (which follows from `HasDerivAt (deriv f) c₂ x₀`)
  forces `f` to be differentiable on a whole neighbourhood of `x₀`;
* if `c₁ = 0 ≠ c₂`, the little-o form of the same statement forces every point `t ≠ x₀` close to
  `x₀` to be a differentiability point of `f` as well.

With differentiability on a neighbourhood in hand, the expansion is the mean value inequality
applied to `t ↦ f t - f x₀ - c₁ * (t - x₀) - c₂ / 2 * (t - x₀)²`, whose derivative is
`o (t - x₀)` by hypothesis.
-/

namespace Work.OddCurve.LowSlope

open Filter Asymptotics
open scoped Topology

noncomputable section

/-- The derivative of the second order error function
`t ↦ f t - f x₀ - c₁ * (t - x₀) - c₂ / 2 * (t - x₀)²` at a differentiability point of `f`. -/
private lemma hasDerivAt_peanoError {f : ℝ → ℝ} {x₀ c₁ c₂ t : ℝ} (hd : DifferentiableAt ℝ f t) :
    HasDerivAt (fun s : ℝ => f s - f x₀ - c₁ * (s - x₀) - c₂ / 2 * ((s - x₀) * (s - x₀)))
      (deriv f t - c₁ - c₂ * (t - x₀)) t := by
  have hA : HasDerivAt (fun s : ℝ => f s - f x₀) (deriv f t) t :=
    hd.hasDerivAt.sub_const (f x₀)
  have hsub : HasDerivAt (fun s : ℝ => s - x₀) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t).sub_const x₀
  have hB : HasDerivAt (fun s : ℝ => c₁ * (s - x₀)) c₁ t := by
    simpa using hsub.const_mul c₁
  have hC : HasDerivAt (fun s : ℝ => c₂ / 2 * ((s - x₀) * (s - x₀))) (c₂ * (t - x₀)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (s - x₀) * (s - x₀)) (2 * (t - x₀)) t := by
      have h := hsub.mul hsub
      convert h using 1 <;> first | rfl | ring
    have h3 := h1.const_mul (c₂ / 2)
    convert h3 using 1 <;> first | rfl | ring
  exact (hA.sub hB).sub hC

/-- **The analytic step.**  If `f` is differentiable on a neighbourhood of `x₀`, `c₁ = deriv f x₀`
and `deriv f` is differentiable at `x₀` with derivative `c₂`, then `f` has the Peano expansion at
`x₀` with coefficients `c₁, c₂`. -/
private lemma peano2_of_eventually_differentiable {f : ℝ → ℝ} {x₀ c₁ c₂ : ℝ}
    (hd : ∀ᶠ t in 𝓝 x₀, DifferentiableAt ℝ f t) (hc₁ : deriv f x₀ = c₁)
    (h₂ : HasDerivAt (deriv f) c₂ x₀) : Peano2 f x₀ c₁ c₂ := by
  obtain ⟨δd, hδdpos, hδd⟩ := Metric.eventually_nhds_iff.mp hd
  rw [Peano2, Asymptotics.isLittleO_iff]
  intro c hc
  -- the little-o form of `HasDerivAt (deriv f) c₂ x₀`, with the explicit `ε = c / 2`
  have hlit : (fun h : ℝ => deriv f (x₀ + h) - deriv f x₀ - h * c₂) =o[𝓝 0] fun h : ℝ => h := by
    simpa [smul_eq_mul] using (hasDerivAt_iff_isLittleO_nhds_zero.mp h₂)
  obtain ⟨δl, hδlpos, hδl⟩ : ∃ δ > 0, ∀ h : ℝ, |h| < δ →
      |deriv f (x₀ + h) - c₁ - h * c₂| ≤ c / 2 * |h| := by
    have hb := hlit.def (show 0 < c / 2 by linarith)
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hb
    refine ⟨δ, hδpos, fun h hh => ?_⟩
    have hdist : dist h 0 < δ := by simpa only [Real.dist_eq, sub_zero] using hh
    have hb' := hδ hdist
    rw [hc₁] at hb'
    simpa only [Real.norm_eq_abs] using hb'
  refine Metric.eventually_nhds_iff.mpr ⟨min δd δl, lt_min hδdpos hδlpos, fun h hh => ?_⟩
  rw [Real.dist_eq, sub_zero] at hh
  have hhd : |h| < δd := lt_of_lt_of_le hh (min_le_left _ _)
  have hhl : |h| < δl := lt_of_lt_of_le hh (min_le_right _ _)
  have habs : ∀ x ∈ Set.Icc (x₀ - |h|) (x₀ + |h|), |x - x₀| ≤ |h| := by
    intro x hx
    rw [abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hdiff : ∀ x ∈ Set.Icc (x₀ - |h|) (x₀ + |h|), DifferentiableAt ℝ
      (fun s : ℝ => f s - f x₀ - c₁ * (s - x₀) - c₂ / 2 * ((s - x₀) * (s - x₀))) x := by
    intro x hx
    have hxδ : dist x x₀ < δd := by
      rw [Real.dist_eq]; exact lt_of_le_of_lt (habs x hx) hhd
    exact (hasDerivAt_peanoError (hδd hxδ)).differentiableAt
  have hbound : ∀ x ∈ Set.Icc (x₀ - |h|) (x₀ + |h|),
      ‖deriv (fun s : ℝ => f s - f x₀ - c₁ * (s - x₀) - c₂ / 2 * ((s - x₀) * (s - x₀))) x‖
        ≤ c / 2 * |h| := by
    intro x hx
    have hxδ : dist x x₀ < δd := by
      rw [Real.dist_eq]; exact lt_of_le_of_lt (habs x hx) hhd
    have hxl : |x - x₀| < δl := lt_of_le_of_lt (habs x hx) hhl
    rw [(hasDerivAt_peanoError (hδd hxδ)).deriv, Real.norm_eq_abs]
    have hb := hδl (x - x₀) hxl
    rw [show x₀ + (x - x₀) = x by ring, mul_comm (x - x₀) c₂] at hb
    exact le_trans hb (mul_le_mul_of_nonneg_left (habs x hx) (by linarith))
  -- the mean value inequality on the symmetric interval around `x₀` of radius `|h|`
  obtain hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
      (f := fun s : ℝ => f s - f x₀ - c₁ * (s - x₀) - c₂ / 2 * ((s - x₀) * (s - x₀)))
      (s := Set.Icc (x₀ - |h|) (x₀ + |h|)) (C := c / 2 * |h|)
      (x := x₀) (y := x₀ + h) hdiff hbound (convex_Icc _ _)
      ⟨by linarith [abs_nonneg h], by linarith [abs_nonneg h]⟩
      ⟨by linarith [neg_abs_le h], by linarith [le_abs_self h]⟩
  simp only [show x₀ + h - x₀ = h by ring, Real.norm_eq_abs] at hmvt
  have hz : f x₀ - f x₀ - c₁ * (x₀ - x₀) - c₂ / 2 * ((x₀ - x₀) * (x₀ - x₀)) = 0 := by ring
  rw [hz, sub_zero] at hmvt
  have hkey : |f (x₀ + h) - f x₀ - c₁ * h - c₂ / 2 * (h * h)| ≤ c * (h * h) := by
    calc |f (x₀ + h) - f x₀ - c₁ * h - c₂ / 2 * (h * h)| ≤ c / 2 * |h| * |h| := hmvt
      _ = c / 2 * (h * h) := by
            rw [show c / 2 * |h| * |h| = c / 2 * (|h| * |h|) by ring, abs_mul_abs_self]
      _ ≤ c * (h * h) := by nlinarith [mul_self_nonneg h, hc]
  have hnormsq : ‖h ^ 2‖ = h ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
  rw [hnormsq, Real.norm_eq_abs]
  simpa only [sq] using hkey

/-- **The differentiability step.**  From `HasDerivAt f c₁ x₀` and
`HasDerivAt (deriv f) c₂ x₀` with `(c₁, c₂) ≠ (0, 0)` it follows that `f` is differentiable on a
neighbourhood of `x₀` (i.e. at all points of some neighbourhood).  This uses the fact that `deriv`
vanishes at the points at which `f` is not differentiable. -/
private lemma eventually_differentiable_of_hasDerivAt_deriv {f : ℝ → ℝ} {x₀ c₁ c₂ : ℝ}
    (h₁ : HasDerivAt f c₁ x₀) (h₂ : HasDerivAt (deriv f) c₂ x₀) (hne : c₁ ≠ 0 ∨ c₂ ≠ 0) :
    ∀ᶠ t in 𝓝 x₀, DifferentiableAt ℝ f t := by
  have hc₁ : deriv f x₀ = c₁ := h₁.deriv
  by_cases hc1zero : c₁ = 0
  · -- `c₁ = 0`, so `c₂ ≠ 0`; every point `t` with `0 < |t - x₀|` small must be differentiable
    have hc2ne : c₂ ≠ 0 := by
      rcases hne with h | h
      · exact absurd hc1zero h
      · exact h
    have hb : ∀ᶠ t : ℝ in 𝓝 x₀,
        ‖deriv f t - deriv f x₀ - (t - x₀) * c₂‖ ≤ |c₂| / 2 * ‖t - x₀‖ := by
      have h1 := (h₂.isLittleO).def (show 0 < |c₂| / 2 from div_pos (abs_pos.mpr hc2ne) two_pos)
      simpa [smul_eq_mul] using h1
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hb
    refine Metric.eventually_nhds_iff.mpr ⟨δ, hδpos, fun t ht => ?_⟩
    by_cases ht0 : t = x₀
    · rw [ht0]; exact h₁.differentiableAt
    · by_contra hnd
      have hd0 : deriv f t = 0 := deriv_zero_of_not_differentiableAt hnd
      have he : deriv f t - deriv f x₀ - (t - x₀) * c₂ = -((t - x₀) * c₂) := by
        rw [hd0, hc₁, hc1zero]; ring
      have hbd := hδ ht
      rw [he] at hbd
      simp only [norm_neg, norm_mul, Real.norm_eq_abs] at hbd
      have hxpos : 0 < |t - x₀| := abs_pos.mpr (sub_ne_zero.mpr ht0)
      have hle : |c₂| ≤ |c₂| / 2 := by
        rw [mul_comm (|c₂| / 2) (|t - x₀|)] at hbd
        exact le_of_mul_le_mul_left hbd hxpos
      have hpos : 0 < |c₂| := abs_pos.mpr hc2ne
      linarith
  · -- `c₁ ≠ 0`: continuity of `deriv f` at `x₀` forces differentiability nearby
    have hb : ∀ᶠ t : ℝ in 𝓝 x₀, |deriv f t - c₁ - (t - x₀) * c₂| ≤ |t - x₀| := by
      have h1 := (h₂.isLittleO).def (show (0 : ℝ) < 1 by norm_num)
      filter_upwards [h1] with t ht
      rw [hc₁, one_mul, smul_eq_mul] at ht
      simpa only [Real.norm_eq_abs] using ht
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hb
    refine Metric.eventually_nhds_iff.mpr ⟨min δ (|c₁| / (2 * (|c₂| + 1))), ?_, fun t ht => ?_⟩
    · refine lt_min hδpos ?_
      have : 0 < |c₁| := abs_pos.mpr hc1zero
      positivity
    · by_contra hnd
      have hd0 : deriv f t = 0 := deriv_zero_of_not_differentiableAt hnd
      have htδ : dist t x₀ < δ := lt_of_lt_of_le ht (min_le_left _ _)
      have hin : |t - x₀| < |c₁| / (2 * (|c₂| + 1)) := by
        have h := lt_of_lt_of_le ht (min_le_right _ _)
        rwa [Real.dist_eq] at h
      have hbd := hδ htδ
      have hA : |c₁| ≤ |t - x₀| * (|c₂| + 1) := by
        have he : c₁ = -(deriv f t - c₁ - (t - x₀) * c₂) - (t - x₀) * c₂ := by
          rw [hd0]; ring
        calc |c₁| = |-(deriv f t - c₁ - (t - x₀) * c₂) - (t - x₀) * c₂| := by
              conv_lhs => rw [he]
          _ ≤ |-(deriv f t - c₁ - (t - x₀) * c₂)| + |(t - x₀) * c₂| := abs_sub _ _
          _ ≤ |t - x₀| + |t - x₀| * |c₂| := by rw [abs_neg, abs_mul]; linarith [hbd]
          _ = |t - x₀| * (|c₂| + 1) := by ring
      have hpos1 : 0 < |c₂| + 1 := by positivity
      have hAB : |t - x₀| * (|c₂| + 1) < |c₁| / 2 := by
        calc |t - x₀| * (|c₂| + 1) < (|c₁| / (2 * (|c₂| + 1))) * (|c₂| + 1) :=
              mul_lt_mul_of_pos_right hin hpos1
          _ = |c₁| / 2 := by field_simp
      linarith [abs_nonneg c₁]

theorem peano2_of_hasDerivAt_deriv {f : ℝ → ℝ} {x₀ c₁ c₂ : ℝ}
    (h₁ : HasDerivAt f c₁ x₀) (h₂ : HasDerivAt (deriv f) c₂ x₀) (hne : c₁ ≠ 0 ∨ c₂ ≠ 0) :
    Work.OddCurve.LowSlope.Peano2 f x₀ c₁ c₂ :=
  peano2_of_eventually_differentiable (eventually_differentiable_of_hasDerivAt_deriv h₁ h₂ hne)
    h₁.deriv h₂

end

end Work.OddCurve.LowSlope
