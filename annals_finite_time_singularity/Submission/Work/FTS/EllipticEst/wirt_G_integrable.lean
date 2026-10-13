import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst

/-- Jordan's inequality on `(0, π)`: `(2/π) * min s (π - s) ≤ sin s`. -/
private theorem sin_min_le_sin {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) Real.pi) :
    2 / Real.pi * min s (Real.pi - s) ≤ Real.sin s := by
  have hm0 : 0 < min s (Real.pi - s) := lt_min hs.1 (by linarith [hs.2])
  have hmle : min s (Real.pi - s) ≤ Real.pi / 2 := by
    rcases le_total s (Real.pi - s) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hsin_eq : Real.sin s = Real.sin (min s (Real.pi - s)) := by
    rcases le_total s (Real.pi - s) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Real.sin_pi_sub]
  rw [hsin_eq]
  exact Real.mul_le_sin hm0.le hmle

/-- **Interval integrability of the squared "Wirtinger quotient" `G`.**

For `a < b`, `r > 0` with `r * (b - a) = π` and `u ∈ C²` on `[a, b]` vanishing at both
endpoints, the function
`x ↦ ((u'(x) sin (r (x - a)) - u(x) r cos (r (x - a))) / sin (r (x - a)))²`
is interval integrable on `[a, b]`.  The quotient has removable singularities at the
endpoints (`u` vanishes to first order there, and the numerator to second order), so the
integrand is bounded on `(a, b)`; being continuous there it is integrable. -/
theorem wirt_G_integrable {a b r : ℝ} (hab : a < b) (hr : 0 < r) (hrb : r * (b - a) = π)
    {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Icc a b)) (ha : u a = 0) (hb : u b = 0) :
    IntervalIntegrable (fun x => ((deriv u x * Real.sin (r * (x - a))
        - u x * (r * Real.cos (r * (x - a)))) / Real.sin (r * (x - a))) ^ 2) volume a b := by
  set g : ℝ → ℝ := fun x => ((deriv u x * Real.sin (r * (x - a))
        - u x * (r * Real.cos (r * (x - a)))) / Real.sin (r * (x - a))) ^ 2
  have hle : a ≤ b := hab.le
  -- ### a uniform bound for the derivative on the closed interval
  have hU : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  have hdiff : DifferentiableOn ℝ u (Set.Icc a b) := hu.differentiableOn (by norm_num)
  have hcontDeriv : ContinuousOn (derivWithin u (Set.Icc a b)) (Set.Icc a b) :=
    hu.continuousOn_derivWithin hU (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontDeriv
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC a ⟨le_rfl, hle⟩)
  have hderivC : ∀ x ∈ Set.Ioo a b, ‖deriv u x‖ ≤ C := by
    intro x hx
    have hnhds : Set.Icc a b ∈ 𝓝 x :=
      mem_of_superset (Ioo_mem_nhds hx.1 hx.2) Set.Ioo_subset_Icc_self
    rw [← derivWithin_of_mem_nhds hnhds]
    exact hC x ⟨hx.1.le, hx.2.le⟩
  -- ### mean value bounds for `u` from both endpoints
  have hu_le_Ca : ∀ x ∈ Set.Ioo a b, ‖u x‖ ≤ C * (x - a) := by
    intro x hx
    have hres := norm_image_sub_le_of_norm_deriv_le_segment hdiff
      (fun y hy => hC y ⟨hy.1, hy.2.le⟩) x ⟨hx.1.le, hx.2.le⟩
    simpa [ha] using hres
  have hu_le_Cb : ∀ x ∈ Set.Ioo a b, ‖u x‖ ≤ C * (b - x) := by
    intro x hx
    have hdiff2 : DifferentiableOn ℝ u (Set.Icc x b) :=
      hdiff.mono (Set.Icc_subset_Icc hx.1.le le_rfl)
    have hbd : ∀ y ∈ Set.Ico x b, ‖derivWithin u (Set.Icc x b) y‖ ≤ C := by
      intro y hy
      rcases lt_or_eq_of_le hy.1 with hylt | hyeq
      · have hnhds : Set.Icc x b ∈ 𝓝 y :=
          mem_of_superset (Ioo_mem_nhds hylt hy.2) Set.Ioo_subset_Icc_self
        rw [derivWithin_of_mem_nhds hnhds]
        exact hderivC y ⟨hx.1.trans hylt, hy.2⟩
      · have hyx : y = x := hyeq.symm
        rw [hyx]
        have hnhdsA : Set.Icc a b ∈ 𝓝 x :=
          mem_of_superset (Ioo_mem_nhds hx.1 hx.2) Set.Ioo_subset_Icc_self
        have hdAt : DifferentiableAt ℝ u x :=
          (hdiff x ⟨hx.1.le, hx.2.le⟩).differentiableAt hnhdsA
        have hder : HasDerivWithinAt u (deriv u x) (Set.Icc x b) x :=
          hdAt.hasDerivAt.hasDerivWithinAt
        rw [hder.derivWithin ((uniqueDiffOn_Icc hx.2).uniqueDiffWithinAt ⟨le_rfl, hx.2.le⟩)]
        exact hderivC x hx
    have hres := norm_image_sub_le_of_norm_deriv_le_segment hdiff2 hbd b ⟨hx.2.le, le_rfl⟩
    simpa [hb] using hres
  -- ### the sine is bounded below on `(a, b)`
  have hslt : ∀ x ∈ Set.Ioo a b, r * (x - a) < Real.pi := by
    intro x hx
    rw [← hrb]
    exact mul_lt_mul_of_pos_left (by linarith [hx.2]) hr
  have hsinpos : ∀ x ∈ Set.Ioo a b, 0 < Real.sin (r * (x - a)) := by
    intro x hx
    exact Real.sin_pos_of_pos_of_lt_pi (mul_pos hr (by linarith [hx.1])) (hslt x hx)
  have hmin_rewrite : ∀ x ∈ Set.Ioo a b,
      r * min (x - a) (b - x) = min (r * (x - a)) (Real.pi - r * (x - a)) := by
    intro x hx
    rw [mul_min_of_nonneg (a := r) (x - a) (b - x) hr.le]
    congr 1
    rw [← hrb]; ring
  have hsin_lb : ∀ x ∈ Set.Ioo a b,
      2 / Real.pi * (r * min (x - a) (b - x)) ≤ Real.sin (r * (x - a)) := by
    intro x hx
    have h := sin_min_le_sin (s := r * (x - a))
      ⟨mul_pos hr (by linarith [hx.1]), hslt x hx⟩
    rwa [← hmin_rewrite x hx] at h
  -- ### `u / sin` is bounded
  have hK : 0 ≤ C * Real.pi / (2 * r) :=
    div_nonneg (mul_nonneg hC0 Real.pi_pos.le) (by linarith)
  have hratio : ∀ x ∈ Set.Ioo a b,
      ‖u x / Real.sin (r * (x - a))‖ ≤ C * Real.pi / (2 * r) := by
    intro x hx
    have hspos : 0 < Real.sin (r * (x - a)) := hsinpos x hx
    have hfm : ‖u x‖ ≤ C * min (x - a) (b - x) := by
      rw [mul_min_of_nonneg (a := C) (x - a) (b - x) hC0]
      exact le_min (hu_le_Ca x hx) (hu_le_Cb x hx)
    rw [norm_div, Real.norm_of_nonneg hspos.le, div_le_iff₀ hspos]
    calc ‖u x‖ ≤ C * min (x - a) (b - x) := hfm
      _ ≤ (C * Real.pi / (2 * r)) * Real.sin (r * (x - a)) := by
        have hcoe : (C * Real.pi / (2 * r)) * (2 / Real.pi * (r * min (x - a) (b - x)))
            = C * min (x - a) (b - x) := by
          have h1 : r ≠ 0 := ne_of_gt hr
          have h2 : Real.pi ≠ 0 := Real.pi_ne_zero
          field_simp
        rw [← hcoe]
        exact mul_le_mul_of_nonneg_left (hsin_lb x hx) hK
  -- ### pointwise bound for the integrand
  have hgbound : ∀ x ∈ Set.Ioo a b, ‖g x‖ ≤ (C + r * (C * Real.pi / (2 * r))) ^ 2 := by
    intro x hx
    have hspos : 0 < Real.sin (r * (x - a)) := hsinpos x hx
    have hd : |deriv u x| ≤ C := by
      have h := hderivC x hx
      rwa [Real.norm_eq_abs] at h
    have huabs : |u x| ≤ (C * Real.pi / (2 * r)) * Real.sin (r * (x - a)) := by
      have h := hratio x hx
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hspos] at h
      rwa [div_le_iff₀ hspos] at h
    have hcos : |Real.cos (r * (x - a))| ≤ 1 := Real.abs_cos_le_one _
    have hkey : |(deriv u x * Real.sin (r * (x - a)) - u x * (r * Real.cos (r * (x - a))))
        / Real.sin (r * (x - a))| ≤ C + r * (C * Real.pi / (2 * r)) := by
      rw [abs_div, abs_of_pos hspos, div_le_iff₀ hspos]
      calc |deriv u x * Real.sin (r * (x - a)) - u x * (r * Real.cos (r * (x - a)))|
          ≤ |deriv u x * Real.sin (r * (x - a))| + |u x * (r * Real.cos (r * (x - a)))| :=
            abs_sub _ _
        _ ≤ C * Real.sin (r * (x - a))
              + ((C * Real.pi / (2 * r)) * Real.sin (r * (x - a))) * (r * 1) := by
            refine add_le_add ?_ ?_
            · rw [abs_mul, abs_of_pos hspos]
              exact mul_le_mul_of_nonneg_right hd hspos.le
            · rw [abs_mul, abs_mul, abs_of_pos hr]
              exact mul_le_mul huabs (mul_le_mul_of_nonneg_left hcos hr.le)
                (mul_nonneg hr.le (abs_nonneg _)) (mul_nonneg hK hspos.le)
        _ = (C + r * (C * Real.pi / (2 * r))) * Real.sin (r * (x - a)) := by ring
    show ‖((deriv u x * Real.sin (r * (x - a)) - u x * (r * Real.cos (r * (x - a))))
        / Real.sin (r * (x - a))) ^ 2‖ ≤ (C + r * (C * Real.pi / (2 * r))) ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hkey 2
  -- ### continuity on the open interval, then integrability by boundedness
  have hgc : ContinuousOn g (Set.Ioo a b) := by
    show ContinuousOn (fun x : ℝ => ((deriv u x * Real.sin (r * (x - a))
        - u x * (r * Real.cos (r * (x - a)))) / Real.sin (r * (x - a))) ^ 2) (Set.Ioo a b)
    have hdf : ContinuousOn (deriv u) (Set.Ioo a b) :=
      (hu.mono Set.Ioo_subset_Icc_self).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hfc : ContinuousOn u (Set.Ioo a b) := hu.continuousOn.mono Set.Ioo_subset_Icc_self
    have hsin : ContinuousOn (fun x : ℝ => Real.sin (r * (x - a))) (Set.Ioo a b) :=
      Real.continuous_sin.comp_continuousOn
        ((continuousOn_id.sub continuousOn_const).const_mul r)
    have hcos : ContinuousOn (fun x : ℝ => Real.cos (r * (x - a))) (Set.Ioo a b) :=
      Real.continuous_cos.comp_continuousOn
        ((continuousOn_id.sub continuousOn_const).const_mul r)
    have hsin_ne : ∀ x ∈ Set.Ioo a b, Real.sin (r * (x - a)) ≠ 0 :=
      fun x hx => ne_of_gt (hsinpos x hx)
    have hA : ContinuousOn (fun x : ℝ => deriv u x * Real.sin (r * (x - a))
        - u x * (r * Real.cos (r * (x - a)))) (Set.Ioo a b) :=
      (hdf.mul hsin).sub (hfc.mul (hcos.const_mul r))
    exact (hA.div hsin hsin_ne).pow 2
  have hsm : AEStronglyMeasurable g (volume.restrict (Set.Ioo a b)) :=
    hgc.aestronglyMeasurable measurableSet_Ioo
  have hmeas : volume.restrict (Set.Ioo a b) = volume.restrict (Set.Ioc a b) :=
    restrict_Ioo_eq_restrict_Ioc
  have hIoc : IntegrableOn g (Set.Ioc a b) volume := by
    refine IntegrableOn.of_bound measure_Ioc_lt_top ?_
      ((C + r * (C * Real.pi / (2 * r))) ^ 2) ?_
    · rw [← hmeas]; exact hsm
    · rw [← hmeas]
      exact ae_restrict_of_forall_mem measurableSet_Ioo hgbound
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).2 hIoc

end Work.FTS.EllipticEst
