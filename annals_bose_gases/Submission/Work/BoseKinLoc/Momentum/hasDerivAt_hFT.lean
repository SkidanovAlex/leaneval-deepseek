import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.BoseKinLoc.Momentum.cubFT_1d
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `hFT' = -mFT`

The one-dimensional factor `hFT t = ∫_{-1/2}^{1/2} cos (t s) ds` of the unit-cube Fourier
symbol is differentiable with

    `HasDerivAt hFT (-(mFT t)) t`,   `mFT t = ∫_{-1/2}^{1/2} s sin (t s) ds`,

which is the coordinate identity behind `fderiv ℝ cubFT q (kcStdBasis i) =
-(mFT (q i)) · ∏ j ≠ i, hFT (q j)` (see `cubFT_1d`).

The proof is the parametric integral theorem (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`)
applied to `F x s = cos (x s)` over the (finite) measure `volume.restrict (Icc (-1/2) (1/2))`:
for a.e. `s`, `y ↦ cos (y s)` has derivative `-s sin (x s)` at `x`, and
`‖-(s sin (x s))‖ ≤ |s|` with `s ↦ |s|` integrable on the interval.  The uniformity in `x`
(witnessed by the bound `|s|`) is what makes the argument work at `t = 0` as well, where the
integrand's `x`-derivative vanishes.

The two auxiliary identities `hFT_eq_intervalIntegral` and `mFT_eq_intervalIntegral` convert
the definitional set integrals over `Icc` into interval integrals.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real

namespace Work.BoseKinLoc.Momentum

set_option autoImplicit false

/-- `hFT` as an interval integral. -/
lemma hFT_eq_intervalIntegral (x : ℝ) :
    hFT x = ∫ s in (-(1/2))..(1/2), Real.cos (x * s) := by
  rw [hFT, MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (by norm_num)).symm

/-- `mFT` as an interval integral. -/
lemma mFT_eq_intervalIntegral (x : ℝ) :
    mFT x = ∫ s in (-(1/2))..(1/2), s * Real.sin (x * s) := by
  rw [mFT, MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (by norm_num)).symm

theorem hasDerivAt_hFT (t : ℝ) : HasDerivAt hFT (-(mFT t)) t := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (-(1/2)) (1/2)) with hμ
  have hF_meas : ∀ᶠ x in 𝓝 t, AEStronglyMeasurable (fun s : ℝ => Real.cos (x * s)) μ :=
    Filter.Eventually.of_forall fun x =>
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mono_measure
        Measure.restrict_le_self
  have hF_int : Integrable (fun s : ℝ => Real.cos (t * s)) μ := by
    rw [hμ]
    exact ContinuousOn.integrableOn_compact isCompact_Icc
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hF'_meas : AEStronglyMeasurable (fun s : ℝ => -(s * Real.sin (t * s))) μ :=
    ((continuous_neg.comp
        (continuous_id.mul (Real.continuous_sin.comp
          (continuous_const.mul continuous_id)))).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  have h_bound : ∀ᵐ s ∂μ, ∀ x ∈ (Set.univ : Set ℝ), ‖(-(s * Real.sin (x * s)))‖ ≤ |s| := by
    refine Filter.Eventually.of_forall fun s x _ => ?_
    rw [Real.norm_eq_abs, abs_neg, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg s) (Real.abs_sin_le_one _)
  have hbound_int : Integrable (fun s : ℝ => |s|) μ := by
    rw [hμ]
    exact ContinuousOn.integrableOn_compact isCompact_Icc continuous_abs.continuousOn
  have h_diff : ∀ᵐ s ∂μ, ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun y : ℝ => Real.cos (y * s)) (-(s * Real.sin (x * s))) x := by
    refine Filter.Eventually.of_forall fun s x _ => ?_
    have h1 : HasDerivAt (fun y : ℝ => y * s) s x := by
      simpa using (hasDerivAt_id x).mul_const s
    have h2 : HasDerivAt (fun y : ℝ => Real.cos (y * s)) (-Real.sin (x * s) * s) x := by
      simpa [Function.comp_def] using (Real.hasDerivAt_cos (x * s)).comp x h1
    rw [show -(s * Real.sin (x * s)) = -Real.sin (x * s) * s by ring]
    exact h2
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x s => Real.cos (x * s)) (F' := fun x s => -(s * Real.sin (x * s)))
    (x₀ := t) (s := Set.univ) (bound := fun s => |s|)
    Filter.univ_mem hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  have hderiv : (∫ s, -(s * Real.sin (t * s)) ∂μ) = -(mFT t) := by
    rw [integral_neg, hμ, mFT]
  rw [hderiv] at key
  have hfun : hFT = fun x => ∫ s, Real.cos (x * s) ∂μ := by
    rw [hμ]
    funext x
    rfl
  rw [hfun]
  exact key

end Work.BoseKinLoc.Momentum
