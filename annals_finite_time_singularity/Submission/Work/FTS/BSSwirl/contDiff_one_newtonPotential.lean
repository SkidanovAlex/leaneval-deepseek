import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.BSSwirl.CdAux
import Submission.Work.FTS.BSSwirl.CdCont
import Submission.Work.FTS.BSSwirl.potDeriv_eq_integral_potKerBall
import Submission.Work.FTS.BSSwirl.tendsto_integral_norm_sub_translate

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSSwirl

/-- **`C¹` of the Newtonian potential.**  Let `ω` be a bounded, a.e. strongly measurable vector
field supported in `closedBall 0 R`, and suppose (this is the content of the Calderón–Zygmund
computation `hasFDerivAt_newtonPotential`) that the Newtonian potential `A ω` is differentiable
everywhere with derivative `potDeriv ω`.  Then `A ω` is `C¹`.

The only point to prove is the **continuity of the derivative**: `potDeriv ω x` is the singular
integral `(4π)⁻¹ ∫ z, (potKer z).smulRight (ω (x+z))`; since `ω` is only bounded and measurable,
the pointwise dominated-convergence theorem cannot be applied directly, and the continuity is
obtained instead from the continuity of translations in `L¹`
(`tendsto_integral_norm_sub_translate`, `continuous_integral_smulRight_shift`), the substitution
`z ↦ z + h` moving the shift from the density onto the integrable cut-off kernel `potKerBall ρ`. -/
theorem contDiff_one_newtonPotential {ω : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) (hbdd : ∀ y, ‖ω y‖ ≤ M)
    (hsupp : ∀ y, ω y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hmeas : MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume)
    (hd : ∀ x, HasFDerivAt (Work.FTS.BSSwirl.newtonPotential ω)
      (Work.FTS.BSSwirl.potDeriv ω x) x) :
    ContDiff ℝ 1 (Work.FTS.BSSwirl.newtonPotential ω) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨Work.FTS.BSSwirl.potDeriv ω, ?_, hd⟩
  rw [continuous_iff_continuousAt]
  intro x₀
  set ρ : ℝ := R + ‖x₀‖ + 2 with hρ
  have htrans : Filter.Tendsto
      (fun h : Work.FTS.BSSwirl.R3 =>
        ∫ z, ‖Work.FTS.BSSwirl.potKerBall ρ (z + h) - Work.FTS.BSSwirl.potKerBall ρ z‖)
      (nhds 0) (nhds 0) :=
    Work.FTS.BSSwirl.tendsto_integral_norm_sub_translate (Work.FTS.BSSwirl.potKerBall ρ)
      (Work.FTS.BSSwirl.integrable_potKerBall ρ)
  have hcont : Continuous
      (fun x : Work.FTS.BSSwirl.R3 =>
        ∫ z, (Work.FTS.BSSwirl.potKerBall ρ z).smulRight (ω (x + z))) :=
    Work.FTS.BSSwirl.continuous_integral_smulRight_shift (Work.FTS.BSSwirl.integrable_potKerBall ρ)
      hbdd hmeas htrans
  refine (hcont.continuousAt.const_smul ((4 * Real.pi)⁻¹)).congr ?_
  filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
  have hx' : ‖x - x₀‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hx
    exact hx
  have hxR : R + ‖x‖ + 1 ≤ ρ := by
    have h1 : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have h2 := norm_add_le (x - x₀) x₀
      rw [sub_add_cancel] at h2
      linarith
    rw [hρ]
    linarith
  exact (Work.FTS.BSSwirl.potDeriv_eq_integral_potKerBall hsupp hxR).symm

end Work.FTS.BSSwirl
