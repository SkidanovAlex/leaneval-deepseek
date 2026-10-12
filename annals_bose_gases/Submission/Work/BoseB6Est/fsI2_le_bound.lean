import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.BoseB6Est.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `I₂` estimate `∫ β(t)²/(2t²)dt ≤ 2π B² T`

FS's mass integral `I₂ = ∫ β(t)²/(2t²)dt` (`eq:I2-integral`) is estimated by
`2πB²T`: in polar coordinates on `ℝ³` the Jacobian `4πr²` cancels the `r⁻²`
of the integrand, leaving `4π∫₀^∞ β(r)²/2 dr ≤ 4π · B²T/2`.

The tools here are the corpus's radial integration formula
`Work.BoseBox.integral_eucNorm3_fun` and the pointwise bounds of `FsKernel`
(`β ≤ B` everywhere, `β = 0` beyond the cutoff `T`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseB6Est

open Submission.BoseGases

/-- **Radial reduction of `fsI2`.** The angular integration of
`(β(nrm t))²/(2 nrm t²)` on `Fin 3 → ℝ` produces the factor `4π r²`, which
cancels the `r⁻²` of the integrand, so that only `∫ β(r)²/2 dr` over the radii
remains. -/
lemma fsI2_eq_radial_oneD (K : FsKernel) :
    fsI2 K = 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), (K.β r) ^ 2 / 2 := by
  rw [fsI2]
  rw [Work.BoseBox.integral_eucNorm3_fun (g := fun r => (K.β r) ^ 2 / (2 * r ^ 2))]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr0 : r ≠ 0 := ne_of_gt hr
  field_simp

/-- **The one-dimensional `I₂` bound** `∫₀^∞ β(r)²/2 dr ≤ B²T/2`: `β²/2` is
supported on `[0,T]` and bounded by `B²/2` there. -/
lemma fsI2_oneD_bound (K : FsKernel) :
    (∫ r in Set.Ioi (0 : ℝ), (K.β r) ^ 2 / 2) ≤ K.B ^ 2 * K.T / 2 := by
  set f : ℝ → ℝ := fun r => (K.β r) ^ 2 / 2 with hf
  -- `f` vanishes to the right of the cutoff, so it is the indicator of `(0,T]` of itself
  have hpoint : ∀ r ∈ Set.Ioi (0:ℝ), f r = (Set.Ioc (0:ℝ) K.T).indicator f r := by
    intro r hr
    by_cases h : r ≤ K.T
    · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hr, h⟩)]
    · rw [Set.indicator_of_notMem (fun hc => h hc.2), hf]
      simp only
      rw [K.support r (lt_of_not_ge h)]
      norm_num
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpoint]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
  have hEm : Set.Ioi (0:ℝ) ∩ Set.Ioc (0:ℝ) K.T = Set.Ioc (0:ℝ) K.T := by
    ext r; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]; tauto
  rw [hEm]
  have hbb : ∀ r ∈ Set.Ioc (0:ℝ) K.T, f r ≤ K.B ^ 2 / 2 := by
    intro r _
    rw [hf]
    simp only
    have h1 : (K.β r) ^ 2 ≤ K.B ^ 2 := pow_le_pow_left₀ (K.nonneg r) (K.bound r) 2
    linarith
  have hfin : volume (Set.Ioc (0:ℝ) K.T) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hfm : AEStronglyMeasurable f (volume.restrict (Set.Ioc (0:ℝ) K.T)) := by
    rw [hf]
    exact ((K.meas.pow_const 2).div_const 2).aestronglyMeasurable.restrict
  have hint : IntegrableOn f (Set.Ioc (0:ℝ) K.T) volume := by
    refine IntegrableOn.of_bound hfin hfm (K.B ^ 2 / 2) ?_
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (by rw [hf]; simp only; positivity)]
    rw [hf]; simp only
    have h1 : (K.β r) ^ 2 ≤ K.B ^ 2 := pow_le_pow_left₀ (K.nonneg r) (K.bound r) 2
    linarith
  have hintc : IntegrableOn (fun _ : ℝ => K.B ^ 2 / 2) (Set.Ioc (0:ℝ) K.T) volume := by
    refine IntegrableOn.of_bound hfin aestronglyMeasurable_const (K.B ^ 2 / 2) ?_
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ∫ r in Set.Ioc (0:ℝ) K.T, f r
      ≤ ∫ r in Set.Ioc (0:ℝ) K.T, (fun _ : ℝ => K.B ^ 2 / 2) r :=
        MeasureTheory.setIntegral_mono_on hint hintc measurableSet_Ioc hbb
    _ = K.B ^ 2 * K.T / 2 := by
        rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith [K.Tnn])]
        ring

/-- **FS's `I₂` estimate** `∫ β(t)²/(2t²)dt ≤ 2πB²T` (`eq:I2-integral`). -/
theorem fsI2_le_bound (K : FsKernel) :
    fsI2 K ≤ 2 * Real.pi * K.B ^ 2 * K.T := by
  calc fsI2 K = 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), (K.β r) ^ 2 / 2 :=
        fsI2_eq_radial_oneD K
    _ ≤ 4 * Real.pi * (K.B ^ 2 * K.T / 2) :=
        mul_le_mul_of_nonneg_left (fsI2_oneD_bound K) (by positivity)
    _ = 2 * Real.pi * K.B ^ 2 * K.T := by ring

end Work.BoseB6Est
