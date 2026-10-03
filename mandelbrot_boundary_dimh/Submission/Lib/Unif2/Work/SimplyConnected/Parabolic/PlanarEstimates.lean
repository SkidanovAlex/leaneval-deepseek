import Mathlib

/-!
# Planar estimates for normalised univalent functions

The elementary planar input for the local boundedness of normalised univalent families: a universal
growth bound for normalised univalent functions on the unit disc (proved in
`Submission.UnivalentCompactness`) is rescaled to an arbitrary disc, giving

* `growthFun C t = ((1+t)/(1-t))^C - 1`, the universal growth function;
* `norm_sub_le_of_growth`: on the disc `ball a R`, a function analytic and injective there with
  `deriv f a ≠ 0` grows away from the centre at most like `R‖deriv f a‖ · growthFun C (‖z-a‖/R)`.
-/

namespace Work.SimplyConnected.Parabolic

open scoped Topology Manifold ContDiff
open Metric Set

noncomputable section

/-- The universal growth function `t ↦ ((1+t)/(1-t))^C - 1` attached to a constant `C > 0`. -/
noncomputable def growthFun (C t : ℝ) : ℝ := ((1 + t) / (1 - t)) ^ C - 1

lemma growthFun_nonneg {C : ℝ} (hC : 0 < C) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    0 ≤ growthFun C t := by
  rw [growthFun]
  have h2 : (1 : ℝ) ≤ (1 + t) / (1 - t) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have h3 : (1 : ℝ) ≤ ((1 + t) / (1 - t)) ^ C := by
    calc (1 : ℝ) = 1 ^ C := (Real.one_rpow C).symm
      _ ≤ _ := Real.rpow_le_rpow zero_le_one h2 hC.le
  linarith

lemma growthFun_mono {C : ℝ} (hC : 0 < C) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) :
    growthFun C s ≤ growthFun C t := by
  rw [growthFun, growthFun]
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have h1s : (0:ℝ) < 1 - s := by linarith
  have h1t : (0:ℝ) < 1 - t := by linarith
  have hkey : (1 + s) / (1 - s) ≤ (1 + t) / (1 - t) := by
    rw [div_le_div_iff₀ h1s h1t]
    nlinarith
  have hpos : (0:ℝ) ≤ (1 + s) / (1 - s) := by positivity
  have := Real.rpow_le_rpow hpos hkey hC.le
  linarith

/-- **Growth from a centre.**  If `f` is analytic and injective on the disc `ball a R` and
`deriv f a ≠ 0`, then away from the centre `f` is controlled by the universal growth function
applied to the normalised distance `‖z - a‖ / R`. -/
theorem norm_sub_le_of_growth {C : ℝ} (_hC : 0 < C)
    (hgrowth : ∀ f : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
      Set.InjOn f (Metric.ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
      ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖f z‖ + 1 ≤ ((1 + ‖z‖) / (1 - ‖z‖)) ^ C)
    {a : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (han : ∀ z ∈ Metric.ball a R, AnalyticAt ℂ f z)
    (hinj : Set.InjOn f (Metric.ball a R)) (hder : deriv f a ≠ 0) :
    ∀ z ∈ Metric.ball a R, ‖f z - f a‖ ≤ R * ‖deriv f a‖ * growthFun C (‖z - a‖ / R) := by
  set c : ℂ := (R : ℂ) * deriv f a with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (by exact_mod_cast hR.ne') hder
  set F : ℂ → ℂ := fun ζ => (f (a + (R : ℂ) * ζ) - f a) * c⁻¹ with hF
  have hFan : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ F ζ := by
    intro ζ hζ
    have hζ' : ‖ζ‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hζ
    have hmem : a + (R : ℂ) * ζ ∈ Metric.ball a R := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : a + (R : ℂ) * ζ - a = (R : ℂ) * ζ := by ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      nlinarith
    have h1 : AnalyticAt ℂ (fun ζ : ℂ => f (a + (R : ℂ) * ζ)) ζ :=
      (han _ hmem).comp (x := ζ) (by fun_prop)
    have h2 : AnalyticAt ℂ (fun ζ : ℂ => f (a + (R : ℂ) * ζ) - f a) ζ := h1.sub analyticAt_const
    rw [hF]
    exact h2.mul analyticAt_const
  have hFinj : Set.InjOn F (Metric.ball (0 : ℂ) 1) := by
    intro ζ₁ hζ₁ ζ₂ hζ₂ heq
    have hmem : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, a + (R : ℂ) * ζ ∈ Metric.ball a R := by
      intro ζ hζ
      have hζ' : ‖ζ‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hζ
      rw [Metric.mem_ball, dist_eq_norm]
      have : a + (R : ℂ) * ζ - a = (R : ℂ) * ζ := by ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      nlinarith
    have hval : f (a + (R : ℂ) * ζ₁) = f (a + (R : ℂ) * ζ₂) := by
      have h := heq
      rw [hF] at h
      have h1 : (f (a + (R : ℂ) * ζ₁) - f a) = (f (a + (R : ℂ) * ζ₂) - f a) :=
        mul_right_cancel₀ (inv_ne_zero hcne) h
      have h2 := congrArg (fun w : ℂ => w + f a) h1
      simpa using h2
    have hz := hinj (hmem ζ₁ hζ₁) (hmem ζ₂ hζ₂) hval
    have : (R : ℂ) * ζ₁ = (R : ℂ) * ζ₂ := by
      simpa using (add_left_cancel hz)
    exact mul_left_cancel₀ (by exact_mod_cast hR.ne') this
  have hF0 : F 0 = 0 := by rw [hF]; simp
  have hFder : deriv F 0 = 1 := by
    have haff : HasDerivAt (fun ζ : ℂ => a + (R : ℂ) * ζ) (R : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (R : ℂ)).const_add a
    have hfd : HasDerivAt f (deriv f a) (a + (R : ℂ) * (0 : ℂ)) := by
      simpa using (han a (by simpa [Metric.mem_ball, dist_eq_norm] using hR)).hasStrictDerivAt.hasDerivAt
    have h1' := HasDerivAt.scomp (0 : ℂ) hfd haff
    have h2' := h1'.sub_const (f a)
    rw [smul_eq_mul] at h2'
    have h3' := h2'.mul_const (c⁻¹)
    have hkey : ((R : ℂ) * deriv f a) * c⁻¹ = 1 := by
      rw [hc]
      exact mul_inv_cancel₀ (mul_ne_zero (by exact_mod_cast hR.ne') hder)
    rw [hkey] at h3'
    rw [hF]
    simpa [Function.comp_def] using h3'.deriv
  intro z hz
  have hzn : ‖z - a‖ < R := by
    have := hz
    rw [Metric.mem_ball, dist_eq_norm] at this
    exact this
  set ζ : ℂ := ((R : ℝ)⁻¹ : ℂ) * (z - a) with hζdef
  have hRc : ((R : ℝ)⁻¹ : ℂ) * (R : ℂ) = 1 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ hR.ne', Complex.ofReal_one]
  have hζn : ‖ζ‖ = ‖z - a‖ / R := by
    rw [hζdef, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      inv_mul_eq_div]
  have hζ1 : ‖ζ‖ < 1 := by
    rw [hζn, div_lt_one hR]; exact hzn
  have hζmem : ζ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hζ1
  have hmul : a + (R : ℂ) * ζ = z := by
    rw [hζdef]
    rw [show (R : ℂ) * (((R : ℝ)⁻¹ : ℂ) * (z - a)) = (((R : ℝ)⁻¹ : ℂ) * (R : ℂ)) * (z - a) by ring,
      hRc, one_mul]
    ring
  have hg := hgrowth F hFan hFinj hF0 hFder ζ hζmem
  have hFval : F ζ = (f z - f a) * c⁻¹ := by
    rw [hF]
    simp only [hmul]
  rw [hFval] at hg
  have hnorm : ‖(f z - f a) * c⁻¹‖ = ‖f z - f a‖ / (R * ‖deriv f a‖) := by
    rw [norm_mul, norm_inv, hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      div_eq_mul_inv]
  rw [hnorm] at hg
  have hRpos : 0 < R * ‖deriv f a‖ := mul_pos hR (norm_pos_iff.mpr hder)
  have hup : ‖f z - f a‖ / (R * ‖deriv f a‖) ≤ growthFun C (‖ζ‖) := by
    have := hg
    rw [growthFun]
    linarith
  rw [hζn] at hup
  rw [div_le_iff₀ hRpos] at hup
  calc ‖f z - f a‖ ≤ growthFun C (‖z - a‖ / R) * (R * ‖deriv f a‖) := hup
    _ = R * ‖deriv f a‖ * growthFun C (‖z - a‖ / R) := by ring

end
end Work.SimplyConnected.Parabolic
