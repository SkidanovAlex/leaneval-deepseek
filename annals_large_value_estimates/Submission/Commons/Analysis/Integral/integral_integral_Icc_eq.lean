import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace Commons.Analysis.Integral

open MeasureTheory intervalIntegral
open scoped Interval Topology

/-- Iterated-integral (triangle) identity: for a continuous `g` on `[a, b]`,
`∫_a^b ∫_a^x g = ∫_a^b (b - t) g t`. -/
theorem integral_integral_Icc_eq (g : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    ∫ x in a..b, (∫ t in a..x, g t) = ∫ t in a..b, ((b - t : ℝ) : ℂ) * g t := by
  have hint : IntegrableOn g ([[a, b]]) volume := by
    rw [Set.uIcc_of_le hab]; exact hg.integrableOn_Icc
  have hv_cont : ContinuousOn (fun x : ℝ => ∫ t in a..x, g t) ([[a, b]]) :=
    continuousOn_primitive_interval hint
  have hgint : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab
  have hconst : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume a b := intervalIntegrable_const
  have hderiv_u : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt (fun t : ℝ => b - t) (-1) x := by
    intro x _
    exact HasDerivAt.const_sub b (hasDerivAt_id (x := x))
  have hderiv_v : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt (fun u : ℝ => ∫ t in a..u, g t) (g x) x := by
    intro x hx
    rw [min_eq_left hab, max_eq_right hab] at hx
    have hmem : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
    have hcx : ContinuousAt g x :=
      (hg.continuousWithinAt hmem).continuousAt (Icc_mem_nhds hx.1 hx.2)
    have hmeas : StronglyMeasurableAtFilter g (𝓝 x) volume :=
      AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
        (hg.aestronglyMeasurable measurableSet_Icc) (Icc_mem_nhds hx.1 hx.2)
    have hintx : IntervalIntegrable g volume a x :=
      (hg.mono (Set.Icc_subset_Icc_right hx.2.le)).intervalIntegrable_of_Icc hx.1.le
    exact integral_hasDerivAt_right hintx hmeas hcx
  have key := integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := fun t : ℝ => b - t) (u' := fun _ : ℝ => (-1 : ℝ))
    (v := fun u : ℝ => ∫ t in a..u, g t) (v' := g)
    (by fun_prop : ContinuousOn (fun t : ℝ => b - t) ([[a, b]]))
    hv_cont hderiv_u hderiv_v hconst hgint
  have hB : (∫ t in a..b, ((b - t : ℝ) : ℂ) * g t) = ∫ x in a..b, (b - x) • g x := by
    apply integral_congr
    intro t _
    simp [Complex.real_smul]
  rw [eq_comm, hB, key]
  simp

end Commons.Analysis.Integral