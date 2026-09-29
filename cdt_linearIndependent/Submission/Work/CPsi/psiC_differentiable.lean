import Mathlib
import Submission.Work.CPsi.psiC_deps

namespace Work.CPsi

open Submission.CDTPlan

/-- `R` is a polynomial, hence entire. -/
theorem differentiable_gobR : Differentiable ℂ gobR := by
  unfold gobR
  fun_prop

/-- On the open unit disc, `R` avoids the branch cut `(-∞,0]` (base analysis), so the principal
square root `√R` is holomorphic there. -/
theorem differentiableOn_gobR_cpow :
    DifferentiableOn ℂ (fun z => (gobR z) ^ (1 / 2 : ℂ)) (Metric.ball 0 1) := by
  apply DifferentiableOn.cpow_const
  · exact differentiable_gobR.differentiableOn
  · intro z hz
    exact gobR_slitPlane_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hz)

/-- The lune map `lune (23/10) = gobL` is holomorphic on the open unit disc. -/
theorem differentiableOn_gobL : DifferentiableOn ℂ gobL (Metric.ball 0 1) := by
  have h2 : DifferentiableOn ℂ (fun z : ℂ => gB * z - gB) (Metric.ball 0 1) := by fun_prop
  unfold gobL
  exact (h2.add differentiableOn_gobR_cpow).div_const (2 * gC)

/-- `ψ_C = -(3/4)·lune(23/10, ·) = -(3/4)·gobL` as functions. -/
theorem psiC_eq_smul_gobL : psiC = fun z => -(3 / 4) * gobL z := by
  funext z
  simp only [Submission.CDTPlan.psiC, lune_eq]

theorem psiC_differentiable : DifferentiableOn ℂ Submission.CDTPlan.psiC (Metric.ball 0 1) := by
  rw [psiC_eq_smul_gobL]
  exact differentiableOn_gobL.const_mul _

end Work.CPsi
