import Mathlib

namespace Work.KMTAreas.A4

open MeasureTheory
open scoped ENNReal

/-- `L¹`-Lipschitz bound for the translate difference of a `C¹` function on `ℝ` with values in
`ℂ`: the mean value identity `g (x + y) - g x = ∫_0^1 deriv g (x + t y) * y dt` together with
translation invariance of Lebesgue measure gives
`∫⁻ x, ‖g x - g (x - y)‖ₑ ≤ ‖y‖ₑ * ∫⁻ x, ‖deriv g x‖ₑ`. -/
theorem diffEnormLe_aux (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g) (y : ℝ) :
    ∫⁻ x : ℝ, ‖g x - g (x - y)‖ₑ ≤ ‖y‖ₑ * ∫⁻ x : ℝ, ‖deriv g x‖ₑ := by
  have hderiv_cont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  -- the chain rule along the segment `t ↦ x + t * y`
  have deriv_comp (x t : ℝ) :
      deriv (fun t : ℝ => g (x + t * y)) t = deriv g (x + t * y) * (y : ℂ) := by
    have h1 : (fun t : ℝ => g (x + t * y)) = fun t : ℝ => g (x + y * t) := by
      funext t; rw [mul_comm]
    rw [h1, deriv_comp_mul_left y (fun u : ℝ => g (x + u)) t]
    rw [deriv_comp_const_add]
    rw [Complex.real_smul, mul_comm y t, mul_comm]
  -- rewrite the translate difference as an additive translate inside the integrand
  have step1 : ∫⁻ x : ℝ, ‖g x - g (x - y)‖ₑ = ∫⁻ x : ℝ, ‖g (x + y) - g x‖ₑ := by
    rw [← lintegral_add_right_eq_self (fun x : ℝ => ‖g x - g (x - y)‖ₑ) y]
    apply lintegral_congr
    intro x
    simp [add_sub_cancel_right]
  rw [step1]
  -- fundamental theorem of calculus along the segment
  have step2 : ∀ x : ℝ,
      ‖g (x + y) - g x‖ₑ ≤ ∫⁻ t in Set.Icc (0:ℝ) 1, ‖deriv g (x + t * y) * (y:ℂ)‖ₑ := by
    intro x
    have hcd : ContDiffOn ℝ 1 (fun t : ℝ => g (x + t * y)) (Set.Icc 0 1) := by
      have h1 : ContDiff ℝ 1 (fun t : ℝ => x + t * y) := by fun_prop
      exact (hg.comp h1).contDiffOn
    have hsub := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hcd (by norm_num : (0:ℝ) ≤ 1)
    simp only [one_mul, zero_mul, add_zero] at hsub
    refine hsub.trans_eq ?_
    apply lintegral_congr
    intro t
    rw [deriv_comp x t]
  -- measurability, for Tonelli
  have hG : AEMeasurable (Function.uncurry (fun x t : ℝ => ‖deriv g (x + t * y) * (y:ℂ)‖ₑ))
      (volume.prod (volume.restrict (Set.Icc (0:ℝ) 1))) := by
    have h1 : Continuous (fun p : ℝ × ℝ => deriv g (p.1 + p.2 * y)) :=
      hderiv_cont.comp (by fun_prop)
    have h2 : Continuous (fun p : ℝ × ℝ => deriv g (p.1 + p.2 * y) * (y:ℂ)) :=
      h1.mul continuous_const
    have h3 : Continuous (fun p : ℝ × ℝ => ‖deriv g (p.1 + p.2 * y) * (y:ℂ)‖ₑ) := h2.enorm
    exact h3.aemeasurable
  -- the inner integral is independent of `t`
  have hinner : ∀ t : ℝ,
      ∫⁻ x : ℝ, ‖deriv g (x + t * y) * (y:ℂ)‖ₑ = ‖y‖ₑ * ∫⁻ x : ℝ, ‖deriv g x‖ₑ := by
    intro t
    have hmeas_t : Measurable (fun x : ℝ => ‖deriv g (x + t * y)‖ₑ) :=
      ((hderiv_cont.comp (by fun_prop)).enorm).measurable
    have hy : ‖(y:ℂ)‖ₑ = ‖y‖ₑ := by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]
    calc ∫⁻ x : ℝ, ‖deriv g (x + t * y) * (y:ℂ)‖ₑ
        = ∫⁻ x : ℝ, ‖deriv g (x + t * y)‖ₑ * ‖(y:ℂ)‖ₑ := by
            apply lintegral_congr; intro x; rw [enorm_mul]
      _ = (∫⁻ x : ℝ, ‖deriv g (x + t * y)‖ₑ) * ‖(y:ℂ)‖ₑ := lintegral_mul_const _ hmeas_t
      _ = (∫⁻ x : ℝ, ‖deriv g x‖ₑ) * ‖(y:ℂ)‖ₑ := by
            rw [lintegral_add_right_eq_self (fun s : ℝ => ‖deriv g s‖ₑ) (t * y)]
      _ = ‖y‖ₑ * ∫⁻ x : ℝ, ‖deriv g x‖ₑ := by rw [hy, mul_comm]
  calc ∫⁻ x : ℝ, ‖g (x + y) - g x‖ₑ
      ≤ ∫⁻ x : ℝ, ∫⁻ t in Set.Icc (0:ℝ) 1, ‖deriv g (x + t * y) * (y:ℂ)‖ₑ :=
        lintegral_mono step2
    _ = ∫⁻ t in Set.Icc (0:ℝ) 1, ∫⁻ x : ℝ, ‖deriv g (x + t * y) * (y:ℂ)‖ₑ :=
        lintegral_lintegral_swap hG
    _ = ∫⁻ t in Set.Icc (0:ℝ) 1, ‖y‖ₑ * ∫⁻ x : ℝ, ‖deriv g x‖ₑ := by
        apply lintegral_congr; intro t; exact hinner t
    _ = ‖y‖ₑ * ∫⁻ x : ℝ, ‖deriv g x‖ₑ := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
        norm_num

/-- `L¹`-Lipschitz bound for the translate difference of a Schwartz function on `ℝ`: the mean
value identity `h x - h (x - y) = ∫_0^1 deriv h (x - t y) * y dt` together with translation
invariance of Lebesgue measure gives `∫⁻ x, ‖h x - h (x - y)‖ₑ ≤ ‖y‖ₑ * ∫⁻ x, ‖deriv h x‖ₑ`.
Needed for the convolution-moment estimate `Work.KMTAreas.A4.offConvMoment`.

Hint: rewrite the left side as `∫⁻ x, ‖h (x + y) - h x‖ₑ` with `lintegral_add_right_eq_self`, use
Mathlib's `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc` for `t ↦ h (x + t * y)` on `Icc 0 1`,
then Tonelli (`lintegral_lintegral_swap` with `ν = volume.restrict (Icc 0 1)`) and translation
invariance in `x`; `volume (Icc 0 1) = 1` finishes it. -/
theorem diffEnormLe (h : SchwartzMap ℝ ℂ) (y : ℝ) :
    ∫⁻ x : ℝ, ‖h x - h (x - y)‖ₑ ≤ ‖y‖ₑ * ∫⁻ x : ℝ, ‖deriv (h : ℝ → ℂ) x‖ₑ :=
  diffEnormLe_aux (h : ℝ → ℂ) (h.smooth 1) y

end Work.KMTAreas.A4
