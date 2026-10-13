import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AngGap.Defs
import Submission.Work.FTS.EllipticEst.AngGap.HardySetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngGap.PhiHCalc

/-- **Pointwise calculus for the weighted Hardy identity.**

If `G = angG h` has derivative `h θ · sin 2θ` at `θ ∈ (0, π/2)`, then the quotient
`V = angV h = G / sin 2θ` has derivative `h θ - 2 cot(2θ) V θ` there (quotient rule,
`(sin 2θ)' = 2 cos 2θ`), and consequently `angPhiH h = 6 V² cot 2θ` has derivative
`angF h θ = (h θ)² - 12 (V θ)² - (h θ - 6 cot(2θ) V θ)²` (product rule together with
`(cot 2θ)' = -2(1 + cot²2θ)`, then `ring`).

This is the identity `h² - 12 V² - (h - 6 cot 2θ V)² = (6 V² cot 2θ)'` of Elgindi's
weighted Hardy inequality, stated pointwise on the open interval.  Note that only `hg`
(and `Work.FTS.EllipticEst.AngGap.hasDerivAt_cot_two` from `Defs.lean`) is needed: no
continuity of `h` is required for the pointwise derivative. -/
theorem deriv_angPhiH (h : ℝ → ℝ)
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (Work.FTS.EllipticEst.AngGap.angG h)
        (h θ * Real.sin (2 * θ)) θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (Work.FTS.EllipticEst.AngGap.angV h)
          (h θ - 2 * Real.cot (2 * θ) * Work.FTS.EllipticEst.AngGap.angV h θ) θ
      ∧ HasDerivAt (Work.FTS.EllipticEst.AngGap.angPhiH h)
          (Work.FTS.EllipticEst.AngGap.angF h θ) θ := by
  intro θ hθ
  have hsinpos : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hsinne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsinpos
  -- `(sin 2θ)' = 2 cos 2θ`
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (2 * y)) (2 * Real.cos (2 * θ)) θ := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * θ)).comp θ (hasDerivAt_const_mul (x := θ) (2 : ℝ))
  -- quotient rule: `V = G / sin 2θ`
  have hV0 := (hg θ hθ).div hsin hsinne
  have hV : HasDerivAt (angV h) (h θ - 2 * Real.cot (2 * θ) * angV h θ) θ := by
    refine hV0.congr_deriv ?_
    rw [Real.cot_eq_cos_div_sin, angV]
    field_simp
  refine ⟨hV, ?_⟩
  -- product rule for `Φ_H = 6 V² cot 2θ`
  have h2 := (hV.pow 2).const_mul 6
  have h3 := h2.mul (hasDerivAt_cot_two θ hθ)
  refine h3.congr_deriv ?_
  rw [angF, angFt]
  simp only [Pi.pow_apply]
  ring

end Work.FTS.EllipticEst.AngGap.PhiHCalc
