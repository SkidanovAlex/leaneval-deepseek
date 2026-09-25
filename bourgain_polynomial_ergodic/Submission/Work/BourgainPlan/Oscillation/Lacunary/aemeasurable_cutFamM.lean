import Mathlib
import Submission.Work.BourgainPlan.Oscillation.Lacunary.dilProfDefs

namespace Work.BourgainPlan.Oscillation.Lacunary

open MeasureTheory Finset
open scoped BigOperators ENNReal

/-- The cut family `cutFamM t r f T ρ i x = ∫_{θ ∈ (0,1]} r θ · 1_{θ ≤ t/⌊ρ^i⌋} · P(θ) · e(-2πi x θ) dθ`
is jointly measurable in `(t, x)`: it is the integral over `θ` of a jointly measurable
integrand against the finite measure `mu01`. -/
theorem aemeasurable_cutFamM (ρ : ℝ) (r : ℝ → ℂ) (hr : Measurable r)
    (f : ℤ → ℂ) (T : Finset ℤ) (i : ℕ) :
    Measurable (fun p : ℝ × ℤ =>
      Work.BourgainPlan.Oscillation.Lacunary.cutFamM p.1 r f T ρ i p.2) := by
  simp only [cutFamM]
  refine (MeasureTheory.StronglyMeasurable.integral_prod_right'
    (f := fun (q : (ℝ × ℤ) × ℝ) =>
      (r q.2 * (if q.2 ≤ q.1.1 / (lacScale ρ i : ℝ) then (1:ℂ) else 0)) * trigP T f q.2 *
        Echar q.1.2 q.2) ?_).measurable
  refine Measurable.stronglyMeasurable ?_
  have h1 : Measurable (fun q : (ℝ × ℤ) × ℝ => r q.2) := hr.comp measurable_snd
  have hite : Measurable (fun q : (ℝ × ℤ) × ℝ =>
      if q.2 ≤ q.1.1 / (lacScale ρ i : ℝ) then (1:ℂ) else 0) :=
    Measurable.ite (measurableSet_le measurable_snd (measurable_fst.fst.div measurable_const))
      measurable_const measurable_const
  have hS : Measurable (fun q : (ℝ × ℤ) × ℝ => trigP T f q.2) := by
    unfold trigP; fun_prop
  have hE : Measurable (fun q : (ℝ × ℤ) × ℝ => Echar q.1.2 q.2) := by
    unfold Echar; fun_prop
  exact ((h1.mul hite).mul hS).mul hE

end Work.BourgainPlan.Oscillation.Lacunary
