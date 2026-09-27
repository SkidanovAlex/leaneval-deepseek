import Mathlib
import Submission.Work.EKLComp.ErgMax.ShiftDefs
import Submission.Work.EKLComp.ErgMax.isClosed_Drho

namespace Work.EKLComp.ErgMax

open MeasureTheory Filter
open Work.EKLContract

theorem psi_step_le (ν : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure ν] {ρ : ℝ}
    (hν : ν (Work.EKLContract.Drho ρ) = 1) (hK : IsCompact (Work.EKLContract.Drho ρ))
    (f : BoundedContinuousFunction Work.EKLContract.X3 ℝ) {u v a b e : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : ∀ z ∈ Work.EKLContract.Drho ρ,
      |f (Work.EKLContract.aPlus a b • z) - f z| ≤ e) :
    |Work.EKLComp.ErgMax.psi ν f (u + a) (v + b) - Work.EKLComp.ErgMax.psi ν f u v| ≤ e := by
  -- `Drho ρ` has full `ν`-measure, so `ν`-a.e. `y` lies in it.
  have hae_drho : ∀ᵐ y ∂ν, y ∈ Drho ρ := by
    rw [MeasureTheory.ae_iff]
    show ν (Drho ρ)ᶜ = 0
    rw [MeasureTheory.measure_compl (isClosed_Drho ρ).measurableSet
      (MeasureTheory.measure_ne_top ν _)]
    simp [MeasureTheory.measure_univ, hν]
  -- `aPlus u v` keeps `Drho ρ` invariant (`u, v ≥ 0`).
  have hae : ∀ᵐ y ∂ν, aPlus u v • y ∈ Drho ρ := by
    filter_upwards [hae_drho] with y hy
    exact aPlus_maps_Drho hu hv hy
  -- the pointwise bound, `ν`-a.e.
  have hbound : ∀ᵐ y ∂ν,
      ‖f (aPlus a b • (aPlus u v • y)) - f (aPlus u v • y)‖ ≤ e := by
    filter_upwards [hae] with y hy
    rw [Real.norm_eq_abs]
    exact he (aPlus u v • y) hy
  -- integrability of the two integrands (bounded by `‖f‖` on a probability space)
  have hGint : Integrable (fun y : X3 => f (aPlus a b • (aPlus u v • y))) ν :=
    Integrable.of_bound (f := fun y : X3 => f (aPlus a b • (aPlus u v • y)))
      (f.continuous.comp ((continuous_const_smul (aPlus a b)).comp
        (continuous_const_smul (aPlus u v)))).aestronglyMeasurable
      ‖f‖ (Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm _))
  have hFint : Integrable (fun y : X3 => f (aPlus u v • y)) ν :=
    Integrable.of_bound (f := fun y : X3 => f (aPlus u v • y))
      (f.continuous.comp (continuous_const_smul (aPlus u v))).aestronglyMeasurable
      ‖f‖ (Filter.Eventually.of_forall (fun y => f.norm_coe_le_norm _))
  -- `aPlus (u+a) (v+b) = aPlus a b * aPlus u v`, so the first integral is the `aPlus a b`-shift
  -- of the second.
  have hpsi : psi ν f (u + a) (v + b) = ∫ y, f (aPlus a b • (aPlus u v • y)) ∂ν := by
    rw [psi_apply]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [aPlus_add_swap a b u v, mul_smul]
  have hdiff : psi ν f (u + a) (v + b) - psi ν f u v
      = ∫ y, (f (aPlus a b • (aPlus u v • y)) - f (aPlus u v • y)) ∂ν := by
    rw [hpsi, psi_apply]
    exact (MeasureTheory.integral_sub hGint hFint).symm
  rw [hdiff]
  calc |∫ y, (f (aPlus a b • (aPlus u v • y)) - f (aPlus u v • y)) ∂ν|
      = ‖∫ y, (f (aPlus a b • (aPlus u v • y)) - f (aPlus u v • y)) ∂ν‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ e * ν.real Set.univ := MeasureTheory.norm_integral_le_of_norm_le_const hbound
    _ = e := by
        rw [MeasureTheory.Measure.real_def, MeasureTheory.measure_univ, ENNReal.toReal_one,
          mul_one]

end Work.EKLComp.ErgMax
