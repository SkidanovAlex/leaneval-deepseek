import Submission.Work.Smooth.Jordan.JordanIndex

open Set MeasureTheory
open scoped Topology

namespace Work.Smooth.Jordan

noncomputable section

/-- **A uniform bound on the difference of two contour integrals of the same `1`-form.** -/
theorem norm_intervalIntegral_div_sub_div_le (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    {x y : ℂ} {a b M δ : ℝ} (hδ : 0 < δ)
    (hM : ∀ t ∈ Set.uIcc a b, ‖f t‖ ≤ M)
    (hx : ∀ t ∈ Set.uIcc a b, δ ≤ ‖g t - x‖)
    (hy : ∀ t ∈ Set.uIcc a b, δ ≤ ‖g t - y‖) :
    ‖(∫ t in a..b, f t / (g t - x)) - (∫ t in a..b, f t / (g t - y))‖
      ≤ (M * ‖y - x‖ / δ ^ 2) * |b - a| := by
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM a Set.left_mem_uIcc)
  have hne_x : ∀ t ∈ Set.uIcc a b, g t - x ≠ 0 := fun t ht hc => by
    have h := hx t ht; rw [hc, norm_zero] at h; linarith
  have hne_y : ∀ t ∈ Set.uIcc a b, g t - y ≠ 0 := fun t ht hc => by
    have h := hy t ht; rw [hc, norm_zero] at h; linarith
  have hfx : IntervalIntegrable (fun t => f t / (g t - x)) volume a b :=
    (hf.continuousOn.div (hg.continuousOn.sub continuousOn_const) hne_x).intervalIntegrable
  have hfy : IntervalIntegrable (fun t => f t / (g t - y)) volume a b :=
    (hf.continuousOn.div (hg.continuousOn.sub continuousOn_const) hne_y).intervalIntegrable
  have hcongr : (∫ t in a..b, (f t / (g t - x) - f t / (g t - y)))
      = ∫ t in a..b, f t * (x - y) / ((g t - x) * (g t - y)) :=
    intervalIntegral.integral_congr (fun t ht => by
      have hA := hne_x t ht
      have hB := hne_y t ht
      field_simp
      ring)
  have hEq : (∫ t in a..b, f t / (g t - x)) - (∫ t in a..b, f t / (g t - y))
      = ∫ t in a..b, f t * (x - y) / ((g t - x) * (g t - y)) := by
    rw [← intervalIntegral.integral_sub hfx hfy, hcongr]
  rw [hEq]
  refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => ?_)
  have ht' := Set.uIoc_subset_uIcc ht
  have h1 : ‖f t‖ ≤ M := hM t ht'
  have h3 : δ ^ 2 ≤ ‖g t - x‖ * ‖g t - y‖ := by
    rw [sq]
    exact mul_le_mul (hx t ht') (hy t ht') hδ.le (le_trans hδ.le (hx t ht'))
  have hnum : ‖f t‖ * ‖y - x‖ ≤ M * ‖y - x‖ :=
    mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  rw [norm_div, norm_mul, norm_mul, norm_sub_rev]
  exact div_le_div₀ (mul_nonneg hMnn (norm_nonneg _)) hnum (by positivity) h3

/-- The derivative of a smooth closed curve is bounded on one period. -/
theorem exists_deriv_bound (c : SmoothPlaneCurve) :
    ∃ M : ℝ, ∀ t ∈ Set.uIcc 0 (2 * Real.pi), ‖deriv c.γ t‖ ≤ M :=
  isCompact_uIcc.exists_bound_of_continuousOn c.continuous_deriv.continuousOn

/-- **The primitive of the winding integrand is Lipschitz in the point on the complement of a
neighbourhood of the trace.** -/
theorem windingPrimitive_diff_bound (c : SmoothPlaneCurve) {x y : ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (hM : ∀ t ∈ Set.uIcc 0 (2 * Real.pi), ‖deriv c.γ t‖ ≤ M)
    (hx : ∀ t ∈ Set.uIcc 0 (2 * Real.pi), δ ≤ ‖c.γ t - x‖)
    (hy : ∀ t ∈ Set.uIcc 0 (2 * Real.pi), δ ≤ ‖c.γ t - y‖) :
    ‖windingPrimitive c y (2 * Real.pi) - windingPrimitive c x (2 * Real.pi)‖
      ≤ (M * (2 * Real.pi) / δ ^ 2) * ‖y - x‖ := by
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  have h := norm_intervalIntegral_div_sub_div_le (fun t => deriv c.γ t) (fun t => c.γ t)
    c.continuous_deriv c.cont (a := 0) (b := 2 * Real.pi) (M := M) (δ := δ) hδ hM hx hy
  rw [sub_zero, abs_of_pos h2π] at h
  have key : (M * ‖y - x‖ / δ ^ 2) * (2 * Real.pi) = (M * (2 * Real.pi) / δ ^ 2) * ‖y - x‖ := by
    ring
  rw [key] at h
  simpa [windingPrimitive, windingIntegrand, norm_sub_rev] using h

/-- **The winding integral is Lipschitz in the point, off a neighbourhood of the trace.** -/
theorem wind_diff_bound (c : SmoothPlaneCurve) {x y : ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (hM : ∀ t ∈ Set.uIcc 0 (2 * Real.pi), ‖deriv c.γ t‖ ≤ M)
    (hx : ∀ t ∈ Set.uIcc 0 (2 * Real.pi), δ ≤ ‖c.γ t - x‖)
    (hy : ∀ t ∈ Set.uIcc 0 (2 * Real.pi), δ ≤ ‖c.γ t - y‖) :
    ‖wind c y - wind c x‖
      ≤ ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * ((M * (2 * Real.pi) / δ ^ 2) * ‖y - x‖) := by
  have h := windingPrimitive_diff_bound c hδ hM hx hy
  have heq : wind c y - wind c x
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹
        * (windingPrimitive c y (2 * Real.pi) - windingPrimitive c x (2 * Real.pi)) := by
    rw [wind_def, wind_def]; ring
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

theorem ind_local (c : SmoothPlaneCurve) {x : ℂ} (hx : x ∉ c.trace) : ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℂ, dist y x < ε → ind c y = ind c x := by
  have hne : c.trace.Nonempty := ⟨c.γ 0, c.mem_trace 0⟩
  have hd : 0 < Metric.infDist x c.trace := (c.isClosed_trace.notMem_iff_infDist_pos hne).mp hx
  have hxbd : ∀ t : ℝ, Metric.infDist x c.trace ≤ ‖c.γ t - x‖ := by
    intro t
    have h := Metric.infDist_le_dist_of_mem (x := x) (c.mem_trace t)
    rwa [dist_eq_norm, norm_sub_rev] at h
  obtain ⟨M, hM⟩ := exists_deriv_bound c
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp [Set.uIcc]))
  set d := Metric.infDist x c.trace with hddef
  have hxd0 : 0 < d := hd
  set δ := d / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδd : δ < d := by rw [hδdef]; linarith
  have hxδ : ∀ t ∈ Set.uIcc (0:ℝ) (2 * Real.pi), δ ≤ ‖c.γ t - x‖ :=
    fun t _ => le_of_lt (lt_of_lt_of_le hδd (hxbd t))
  set A := ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * (M * (2 * Real.pi) / δ ^ 2) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (norm_nonneg _) (div_nonneg (mul_nonneg hMnn (by positivity)) (by positivity))
  refine ⟨min δ (1 / (2 * (A + 1))), lt_min hδ (by positivity), fun y hy => ?_⟩
  have hyε : ‖y - x‖ < min δ (1 / (2 * (A + 1))) := by rwa [dist_eq_norm] at hy
  have hyδ : ‖y - x‖ < δ := lt_of_lt_of_le hyε (min_le_left _ _)
  have hytrace : y ∉ c.trace := by
    rintro ⟨t, rfl⟩
    have h1 := hxbd t
    rw [hddef] at h1
    linarith
  have hyδ' : ∀ t ∈ Set.uIcc (0:ℝ) (2 * Real.pi), δ ≤ ‖c.γ t - y‖ := by
    intro t _
    have h1 : d ≤ ‖c.γ t - x‖ := by have := hxbd t; rw [hddef]; exact this
    have h2 : ‖c.γ t - x‖ - ‖y - x‖ ≤ ‖c.γ t - y‖ := by
      have h3 := norm_sub_norm_le (c.γ t - x) (y - x)
      rwa [show (c.γ t - x) - (y - x) = c.γ t - y from by ring] at h3
    rw [hδdef] at *
    linarith
  have hbound : ‖wind c y - wind c x‖ ≤ A * ‖y - x‖ := by
    have h := wind_diff_bound c hδ hM hxδ hyδ'
    rw [hAdef]
    refine le_trans h (le_of_eq ?_)
    ring
  have hAeps : A * ‖y - x‖ ≤ 1 / 2 := by
    have h1 : ‖y - x‖ ≤ 1 / (2 * (A + 1)) := le_of_lt (lt_of_lt_of_le hyε (min_le_right _ _))
    have h2 : A * ‖y - x‖ ≤ A * (1 / (2 * (A + 1))) :=
      mul_le_mul_of_nonneg_left h1 hAnn
    have h3 : A * (1 / (2 * (A + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hnorm : ‖wind c y - wind c x‖ ≤ 1 / 2 := le_trans hbound hAeps
  obtain ⟨k, hk⟩ := wind_mem_int c hytrace
  obtain ⟨l, hl⟩ := wind_mem_int c hx
  have hkl : k = l := by
    by_contra hne'
    have hge : (1:ℝ) ≤ ‖((k - l : ℤ) : ℂ)‖ := by
      rw [Complex.norm_intCast, ← Int.cast_abs]
      have h4 : (1:ℤ) ≤ |k - l| := Int.one_le_abs (sub_ne_zero.mpr hne')
      exact_mod_cast h4
    have hle : ‖((k - l : ℤ) : ℂ)‖ ≤ 1 / 2 := by
      have hcast : ((k - l : ℤ) : ℂ) = (k : ℂ) - (l : ℂ) := by push_cast; ring
      rw [hcast, ← hk, ← hl]
      exact hnorm
    linarith
  have hyy : (ind c y : ℂ) = wind c y := ind_spec c ⟨k, hk⟩
  have hxx : (ind c x : ℂ) = wind c x := ind_spec c ⟨l, hl⟩
  exact Int.cast_injective (by rw [hyy, hxx, hk, hl, hkl])

end

end Work.Smooth.Jordan
