import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.TanTheta.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TanTheta

/-- The slice variable `ψ θ = u θ / cos θ` is `C²` on the open interval `(0, π/2)` whenever
`u` is `C²` on the open neighbourhood `(-1, π/2 + 1)` of `[0, π/2]`.

Route: `ContDiffOn.mono` restricts to `Set.Ioo 0 (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1)`,
then `ContDiffOn.div` with `contDiffOn_cos`, the side condition `Real.cos θ ≠ 0` coming from
`Real.cos_pos_of_mem_Ioo`. -/
theorem psi_contdiff (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo (-1) (Real.pi / 2 + 1))) :
    ContDiffOn ℝ 2 (Work.FTS.EllipticEst.TanTheta.psi u) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 := by
    intro θ hθ hcos
    have hpos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    linarith
  exact (hu.mono hsub).div Real.contDiff_cos.contDiffOn hne

end Work.FTS.EllipticEst.TanTheta
