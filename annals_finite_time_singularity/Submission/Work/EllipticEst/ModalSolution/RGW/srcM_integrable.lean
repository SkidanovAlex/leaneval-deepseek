import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.EllipticEst.ModalSolution.RGW.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the lower source kernel `srcM` near `0`

For `0 < α ≤ 1` the kernel `srcM α m c t = c t · t^{(2m+5)/α - 1}` of the lower
(the harmless) end of the radial Green's function is integrable on `(0, b]`, whenever
`c²` is integrable on `(0, ∞)` and `c` is a.e. strongly measurable there.

Indeed the exponent `p = (2m+5)/α - 1` satisfies `p ≥ 4 > 0` (because `α ≤ 1`), so
`t ↦ t^p` is bounded by `b^p` on `(0,b]`; and the `L²` hypothesis on `c` gives the
pointwise `L¹` bound `‖c t‖ ≤ (c t ^ 2 + 1)/2`, the constant `1` being integrable on
the finite measure space `(0,b]`.
-/

set_option linter.unusedVariables false

namespace Work.EllipticEst.ModalSolution.RGW

theorem srcM_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (Work.EllipticEst.ModalSolution.RadGreenWeak.srcM α m c)
      (Set.Ioc 0 b) := by
  -- unfold `srcM` and abbreviate its exponent
  change MeasureTheory.Integrable (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
    (MeasureTheory.volume.restrict (Set.Ioc 0 b))
  set p : ℝ := (2 * (m : ℝ) + 5) / α - 1 with hp
  have hsubset : Set.Ioc (0 : ℝ) b ⊆ Set.Ioi (0 : ℝ) := fun t ht => ht.1
  -- the exponent is at least `4`
  have h5 : (5 : ℝ) ≤ 2 * (m : ℝ) + 5 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hone : (1 : ℝ) ≤ 1 / α := by
    have h := one_div_le_one_div_of_le hα hα1
    simpa using h
  have hdiv : (5 : ℝ) ≤ (2 * (m : ℝ) + 5) / α := by
    have h2 : (5 : ℝ) ≤ 5 / α := by
      have h := mul_le_mul_of_nonneg_left hone (by norm_num : (0 : ℝ) ≤ 5)
      simpa only [div_eq_mul_inv, mul_one, one_mul] using h
    have h1 : (5 : ℝ) / α ≤ (2 * (m : ℝ) + 5) / α := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h5 (inv_nonneg.mpr hα.le)
    linarith
  have hp4 : (4 : ℝ) ≤ p := by
    rw [hp]
    linarith
  have hp0 : (0 : ℝ) ≤ p := by linarith
  -- the dominating function and its integrability
  have hc2 : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2) (Set.Ioc 0 b) :=
    hc.mono_set hsubset
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 b) :=
    MeasureTheory.integrableOn_const
      (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hsum : MeasureTheory.IntegrableOn (fun t : ℝ => c t ^ 2 + 1) (Set.Ioc 0 b) :=
    hc2.add h1
  have hdom : MeasureTheory.Integrable
      (fun t : ℝ => b ^ p / 2 * (c t ^ 2 + 1)) (MeasureTheory.volume.restrict (Set.Ioc 0 b)) :=
    MeasureTheory.Integrable.const_mul hsum (b ^ p / 2)
  -- a.e. strong measurability of `srcM α m c`
  have hcm' : MeasureTheory.AEStronglyMeasurable c
      (MeasureTheory.volume.restrict (Set.Ioc 0 b)) :=
    hcm.mono_measure (MeasureTheory.Measure.restrict_mono hsubset le_rfl)
  have hpfun : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ p)
      (MeasureTheory.volume.restrict (Set.Ioc 0 b)) :=
    (Real.continuous_rpow_const hp0).aestronglyMeasurable
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * t ^ p)
      (MeasureTheory.volume.restrict (Set.Ioc 0 b)) :=
    MeasureTheory.AEStronglyMeasurable.mul hcm' hpfun
  -- the pointwise bound on `(0, b]`
  have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc 0 b)),
      ‖c t * t ^ p‖ ≤ b ^ p / 2 * (c t ^ 2 + 1) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have htp : t ^ p ≤ b ^ p := Real.rpow_le_rpow ht0.le ht.2 hp0
    have htp0 : (0 : ℝ) ≤ t ^ p := Real.rpow_nonneg ht0.le p
    have hcb : ‖c t‖ ≤ (c t ^ 2 + 1) / 2 := by
      have hsq : ‖c t‖ ^ 2 = c t ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      have hq : (0 : ℝ) ≤ (‖c t‖ - 1) ^ 2 := sq_nonneg _
      nlinarith [hsq, hq]
    have hcb0 : (0 : ℝ) ≤ (c t ^ 2 + 1) / 2 := by positivity
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg htp0]
    calc ‖c t‖ * t ^ p ≤ ((c t ^ 2 + 1) / 2) * t ^ p :=
          mul_le_mul_of_nonneg_right hcb htp0
      _ ≤ ((c t ^ 2 + 1) / 2) * b ^ p := mul_le_mul_of_nonneg_left htp hcb0
      _ = b ^ p / 2 * (c t ^ 2 + 1) := by ring
  exact MeasureTheory.Integrable.mono' hdom hmeas hbound

end Work.EllipticEst.ModalSolution.RGW
