import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.Eps

open MeasureTheory Set

/-- Polar coordinates in `ℝ^3`: the exterior of a ball of radius `κ > 0` is decomposed in
spherical shells, so integrability of a radial function `f ‖·‖` on `{κ ≤ ‖x‖}` is
equivalent to integrability of `r ↦ r^{3-1} • f r = r^2 * f r` on `(κ, ∞)`. -/
theorem exterior_norm_integrable {N : ℕ} {κ : ℝ} (hκ : 0 < κ) :
    MeasureTheory.IntegrableOn (fun p : EuclideanSpace ℝ (Fin 3) => (‖p‖ ^ N)⁻¹)
        {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖} MeasureTheory.volume ↔
      MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * (r ^ N)⁻¹) (Set.Ioi κ)
        MeasureTheory.volume := by
  have hS : MeasurableSet {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  -- The indicator of the exterior set is a function of `‖·‖` only.
  have hfac : {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖}.indicator
        (fun p : EuclideanSpace ℝ (Fin 3) => (‖p‖ ^ N)⁻¹)
      = fun p : EuclideanSpace ℝ (Fin 3) => ((Ici κ).indicator (fun t : ℝ => (t ^ N)⁻¹)) ‖p‖ := by
    funext p
    by_cases hp : κ ≤ ‖p‖
    · rw [Set.indicator_of_mem (show p ∈ {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖} from hp),
        Set.indicator_of_mem (show ‖p‖ ∈ Ici κ from hp)]
    · rw [Set.indicator_of_notMem (show p ∉ {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖} from hp),
        Set.indicator_of_notMem (show ‖p‖ ∉ Ici κ from hp)]
  -- The radial part of the polar-coordinate integrand is the indicator of `Ici κ` times `r^2 * r^{-N}`.
  have hfun : (fun y : ℝ => y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) •
        ((Ici κ).indicator (fun t : ℝ => (t ^ N)⁻¹)) y)
      = (Ici κ).indicator (fun y : ℝ => y ^ 2 * (y ^ N)⁻¹) := by
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    funext y
    rw [hfr, show (3 : ℕ) - 1 = 2 from by norm_num, smul_eq_mul]
    by_cases hy : y ∈ Ici κ
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  -- It is supported in `Ioi 0` because `κ > 0`.
  have hsupp : Function.support ((Ici κ).indicator (fun y : ℝ => y ^ 2 * (y ^ N)⁻¹)) ⊆ Ioi 0 := by
    intro y hy
    by_contra h
    simp only [mem_Ioi, not_lt] at h
    have : y ∉ Ici κ := by simp only [mem_Ici, not_le]; linarith
    exact hy (by simp [Set.indicator_of_notMem, this])
  calc
    IntegrableOn (fun p : EuclideanSpace ℝ (Fin 3) => (‖p‖ ^ N)⁻¹)
        {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖} volume
      ↔ Integrable ({q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖}.indicator
          (fun p : EuclideanSpace ℝ (Fin 3) => (‖p‖ ^ N)⁻¹)) volume :=
          (integrable_indicator_iff hS).symm
    _ ↔ Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
          ((Ici κ).indicator (fun t : ℝ => (t ^ N)⁻¹)) ‖p‖) volume := by
          rw [hfac]
    _ ↔ IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) •
          ((Ici κ).indicator (fun t : ℝ => (t ^ N)⁻¹)) y) (Ioi 0) volume :=
          integrable_fun_norm_addHaar volume
    _ ↔ IntegrableOn ((Ici κ).indicator (fun y : ℝ => y ^ 2 * (y ^ N)⁻¹)) (Ioi 0) volume := by
          rw [hfun]
    _ ↔ Integrable ((Ici κ).indicator (fun y : ℝ => y ^ 2 * (y ^ N)⁻¹)) volume :=
          integrableOn_iff_integrable_of_support_subset hsupp
    _ ↔ IntegrableOn (fun y : ℝ => y ^ 2 * (y ^ N)⁻¹) (Ici κ) volume :=
          integrable_indicator_iff measurableSet_Ici
    _ ↔ IntegrableOn (fun y : ℝ => y ^ 2 * (y ^ N)⁻¹) (Ioi κ) volume := by
          rw [IntegrableOn, IntegrableOn,
            Measure.restrict_congr_set (Ioi_ae_eq_Ici (μ := (volume : Measure ℝ)))]

end Work.BoseFixB3.Eps
