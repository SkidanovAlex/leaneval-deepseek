import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

/-- Basic facts about the angular weight `thEta θ = sin(2θ)^{-η}` (`η = 99/100`) on the
open angular interval `(0, π/2)`: it is strictly positive, it is `≥ 1`, its inverse is
`sin(2θ)^{η}`, and it is continuous there.

All four are immediate from `0 < sin(2θ) ≤ 1` on that interval: the totalised real power
`x ↦ x^p` is positive for `x > 0`, is `≤ 1` for `x ≤ 1` and `p ≤ 0`, satisfies
`x^{-p} = (x^p)⁻¹` for `x ≥ 0`, and is continuous where the base does not vanish. -/
theorem thEtaFacts :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Work.FTS.EllipticEst.thEta θ) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 1 ≤ Work.FTS.EllipticEst.thEta θ) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (Work.FTS.EllipticEst.thEta θ)⁻¹
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) ∧
    ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ hθ
    rw [Work.FTS.EllipticEst.thEta]
    exact Real.rpow_pos_of_pos (hsin θ hθ) _
  · intro θ hθ
    rw [Work.FTS.EllipticEst.thEta]
    have hs := hsin θ hθ
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hη0 : (0 : ℝ) ≤ Work.Spaces.eta := Work.Spaces.eta_pos.le
    have hspow : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ 1 := Real.rpow_le_one hs.le hs1 hη0
    have hpos : 0 < (Real.sin (2 * θ)) ^ Work.Spaces.eta := Real.rpow_pos_of_pos hs _
    rw [Real.rpow_neg hs.le, inv_eq_one_div]
    rw [le_div_iff₀ hpos, one_mul]
    exact hspow
  · intro θ hθ
    rw [Work.FTS.EllipticEst.thEta, Real.rpow_neg (hsin θ hθ).le, inv_inv]
  · refine ContinuousOn.rpow_const ?_ ?_
    · exact Real.continuous_sin.comp_continuousOn
        ((continuous_const.mul continuous_id).continuousOn)
    · intro θ hθ
      exact Or.inl (ne_of_gt (hsin θ hθ))

end Work.EllipticEst.Core
