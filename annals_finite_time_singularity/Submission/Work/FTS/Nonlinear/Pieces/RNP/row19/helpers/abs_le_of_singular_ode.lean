import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row19.helpers

open MeasureTheory Set Filter
open scoped Real

/-- If `u` is continuous on `[0, z]`, differentiable on `(0, z)`, satisfies the singular ODE
`α t u'(t) + 2 u(t) + W(t) = 0` on `(0, z)`, has `u 0 = 0`, and `|W t| ≤ C t` on `[0, z]`,
then `|u z| ≤ C z`.

The homogeneous equation is solved by `u = t ^ (-2/α)` and the boundary condition at `0`
kills the singular homogeneous solution; the estimate comes from the explicit formula
`u(z) = -(1/α) z^(-2/α) ∫_0^z W(t) t^(2/α - 1) dt` together with
`∫_0^z t^(2/α) dt = z^(2/α + 1)/(2/α + 1)`. -/
theorem abs_le_of_singular_ode {u W : ℝ → ℝ} {α C z : ℝ}
    (hα : 0 < α) (hz : 0 < z) (hC : 0 ≤ C)
    (hu_cont : ContinuousOn u (Set.Icc 0 z))
    (hu_diff : ∀ t ∈ Set.Ioo 0 z, HasDerivAt u (deriv u t) t)
    (hode : ∀ t ∈ Set.Ioo 0 z, α * t * deriv u t + 2 * u t + W t = 0)
    (hW_cont : ContinuousOn W (Set.Icc 0 z))
    (hW : ∀ t ∈ Set.Icc 0 z, |W t| ≤ C * t)
    (hu0 : u 0 = 0) :
    |u z| ≤ C * z := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hle0z : (0 : ℝ) ≤ z := le_of_lt hz
  -- The exponent `p = 2/α` and the integrating factor `t ^ p`.
  set p : ℝ := 2 / α with hpdef
  have hp_pos : 0 < p := by rw [hpdef]; positivity
  have hpne : p ≠ 0 := ne_of_gt hp_pos
  set F : ℝ → ℝ := fun t => t ^ p * u t with hFdef
  set f : ℝ → ℝ := fun t => -(1 / α) * (W t * t ^ (p - 1)) with hfdef
  have hpow_cont : Continuous (fun t : ℝ => t ^ p) := Real.continuous_rpow_const hp_pos.le
  -- `F` is continuous on `[0, z]` and has the derivative `f` on `(0, z)`.
  have hF_cont : ContinuousOn F (Set.Icc 0 z) := by
    rw [hFdef]
    exact (hpow_cont.continuousOn).mul hu_cont
  have hF0 : F 0 = 0 := by
    rw [hFdef]
    simp [Real.zero_rpow hpne, hu0]
  have hF_deriv : ∀ t ∈ Set.Ioo 0 z, HasDerivAt F (f t) t := by
    intro t ht
    have htpos : 0 < t := ht.1
    have htp : t ^ p = t ^ (p - 1) * t := by
      have h := Real.rpow_add htpos (p - 1) 1
      rw [Real.rpow_one] at h
      rw [show p - 1 + 1 = p by ring] at h
      exact h
    have hdiv : t * deriv u t = -(2 * u t + W t) / α := by
      rw [eq_div_iff hαne]
      linarith [hode t ht]
    have hinner : p * u t + t * deriv u t = -(1 / α) * W t := by
      rw [hdiv, hpdef]
      field_simp
      ring
    have key : (p * t ^ (p - 1)) * u t + t ^ p * deriv u t
        = -(1 / α) * (W t * t ^ (p - 1)) := by
      have e1 : (p * t ^ (p - 1)) * u t + t ^ p * deriv u t
          = t ^ (p - 1) * (p * u t + t * deriv u t) := by
        rw [htp]; ring
      rw [e1, hinner]; ring
    rw [hFdef, hfdef]
    exact ((Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt htpos))).mul
      (hu_diff t ht)).congr_deriv key
  -- `f` is integrable on `[0, z]` (dominated by `(C/α) t ^ p`).
  have hf_contOn : ContinuousOn f (Set.Ioc 0 z) := by
    rw [hfdef]
    refine ContinuousOn.mul continuousOn_const ?_
    refine (hW_cont.mono ?_).mul ?_
    · intro x hx; exact ⟨le_of_lt hx.1, hx.2⟩
    · intro x hx
      exact (Real.continuousAt_rpow_const x (p - 1) (Or.inl (ne_of_gt hx.1))).continuousWithinAt
  have hf_aesm : AEStronglyMeasurable f (volume.restrict (Set.Ioc 0 z)) :=
    hf_contOn.aestronglyMeasurable measurableSet_Ioc
  have hpt : ∀ x ∈ Set.Ioc 0 z, ‖f x‖ ≤ (C / α) * x ^ p := by
    intro x hx
    have hxpos : 0 < x := hx.1
    have hWx : |W x| ≤ C * x := hW x ⟨le_of_lt hx.1, hx.2⟩
    have h1α : 0 < 1 / α := by positivity
    have hxrn : 0 ≤ x ^ (p - 1) := Real.rpow_nonneg (le_of_lt hxpos) _
    have hxr : x ^ (p - 1) * x = x ^ p := by
      have h := Real.rpow_add hxpos (p - 1) 1
      rw [Real.rpow_one] at h
      rw [show p - 1 + 1 = p by ring] at h
      exact h.symm
    rw [hfdef, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos h1α, abs_mul,
      abs_of_nonneg hxrn]
    calc 1 / α * (|W x| * x ^ (p - 1)) ≤ 1 / α * ((C * x) * x ^ (p - 1)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hWx hxrn) (le_of_lt h1α)
      _ = (C / α) * x ^ p := by rw [← hxr]; ring
  have hg_int : IntervalIntegrable (fun t : ℝ => (C / α) * t ^ p) volume 0 z :=
    Continuous.intervalIntegrable (continuous_const.mul hpow_cont) 0 z
  have hf_int : IntervalIntegrable f volume 0 z := by
    refine IntervalIntegrable.mono_fun' hg_int ?_ ?_
    · rw [Set.uIoc_of_le hle0z]; exact hf_aesm
    · rw [Filter.EventuallyLE, Set.uIoc_of_le hle0z]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hpt
  -- Fundamental theorem of calculus: `F z = ∫_0^z f`.
  have hftc : ∫ t in (0 : ℝ)..z, f t = F z - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle0z hF_cont hF_deriv hf_int
  have hFz : F z = ∫ t in (0 : ℝ)..z, f t := by rw [hftc, hF0]; ring
  have h1 : |F z| ≤ ∫ t in (0 : ℝ)..z, |f t| := by
    rw [hFz]
    exact intervalIntegral.abs_integral_le_integral_abs hle0z
  have h2 : ∫ t in (0 : ℝ)..z, |f t| ≤ ∫ t in (0 : ℝ)..z, (C / α) * t ^ p :=
    intervalIntegral.integral_mono_on_of_le_Ioo hle0z hf_int.abs hg_int
      (fun t ht => by
        have h := hpt t ⟨ht.1, ht.2.le⟩
        rwa [Real.norm_eq_abs] at h)
  have h3 : ∫ t in (0 : ℝ)..z, (C / α) * t ^ p = (C / α) * (z ^ (p + 1) / (p + 1)) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [integral_rpow (Or.inl (by linarith [hp_pos] : -1 < p))]
    rw [Real.zero_rpow (by linarith [hp_pos] : p + 1 ≠ 0)]
    ring
  have h4 : |F z| ≤ (C / α) * (z ^ (p + 1) / (p + 1)) := h1.trans (h2.trans (le_of_eq h3))
  have hzp : 0 < z ^ p := Real.rpow_pos_of_pos hz p
  have hzpz : z ^ (p + 1) = z ^ p * z := by
    have h := Real.rpow_add hz p 1
    rw [Real.rpow_one] at h
    exact h
  -- `1/(α (p+1)) = 1/(α + 2) ≤ 1`.
  have hcoef : 1 / (α * (p + 1)) ≤ 1 := by
    have hpos : 0 < α * (p + 1) := by positivity
    rw [div_le_iff₀ hpos]
    have hge : 1 ≤ α * (p + 1) := by
      rw [hpdef]
      have : α * (2 / α + 1) = 2 + α := by field_simp
      rw [this]; linarith
    simpa using hge
  have hFbound2 : |F z| ≤ C * z * z ^ p := by
    calc |F z| ≤ (C / α) * (z ^ (p + 1) / (p + 1)) := h4
      _ = (C * z * z ^ p) * (1 / (α * (p + 1))) := by
          rw [hzpz]; field_simp
      _ ≤ (C * z * z ^ p) * 1 := mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ = C * z * z ^ p := by ring
  have huabs : |u z| = |F z| / z ^ p := by
    have hFz' : F z = z ^ p * u z := by rw [hFdef]
    rw [hFz', abs_mul, abs_of_pos hzp, eq_div_iff (ne_of_gt hzp)]
    ring
  calc |u z| = |F z| / z ^ p := huabs
    _ ≤ (C * z * z ^ p) / z ^ p := div_le_div_of_nonneg_right hFbound2 (le_of_lt hzp)
    _ = C * z := by rw [div_eq_iff (ne_of_gt hzp)]

end Work.FTS.Nonlinear.Pieces.RNP.row19.helpers
