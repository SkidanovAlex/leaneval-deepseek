import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn

/-- **Integrability of a continuous field paired with a compactly supported gradient.**

If `ω` is continuous and `ψ` is `C¹` with compact support, then `y ↦ ⟪ω y, ∇ψ y⟫` is integrable:
`∇ψ = 0` off the (compact) support of `ψ`, and on it `ω` is bounded because it is continuous
there.  Concretely, the function is continuous and compactly supported: continuity via
`⟪ω y, ∇ψ y⟫ = fderiv ℝ ψ y (ω y)` (`inner_gradient_right`) and the joint continuity of the
Fréchet derivative of a `C¹` map, compact support via `HasCompactSupport.mono'` and
`gradient_eq` for eventually-equal functions. -/
theorem integrable_inner_gradient {ω : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3}
    {ψ : Work.FTS.PressureOn.R3 → ℝ}
    (hωcont : Continuous ω) (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun y => inner ℝ (ω y) (gradient ψ y)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · -- continuity: rewrite the inner product as the Fréchet derivative applied to `ω`
    have hfderiv : Continuous fun p : R3 × R3 => (fderiv ℝ ψ p.1) p.2 :=
      hψ.continuous_fderiv_apply (by norm_num)
    have hpair : Continuous fun y : R3 => (y, ω y) := continuous_id.prodMk hωcont
    have hcont : Continuous fun y : R3 => (fderiv ℝ ψ y) (ω y) := hfderiv.comp hpair
    refine hcont.congr ?_
    intro y
    rw [inner_gradient_right, starRingEnd_apply, star_trivial]
  · -- compact support: off `tsupport ψ` the gradient vanishes
    refine hψcs.mono' ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hcon
    have h0 : ψ =ᶠ[nhds y] 0 := notMem_tsupport_iff_eventuallyEq.mp hcon
    have hgrad : gradient ψ y = 0 := by
      rw [h0.gradient_eq]
      change gradient (fun _ : R3 => (0 : ℝ)) y = 0
      exact gradient_fun_const y 0
    exact hy (by rw [hgrad, inner_zero_right])

end Work.FTS.PressureOn
