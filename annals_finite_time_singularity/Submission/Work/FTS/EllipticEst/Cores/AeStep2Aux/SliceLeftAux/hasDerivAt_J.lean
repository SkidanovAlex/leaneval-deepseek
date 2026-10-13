import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.SliceLeftAux

/-- The derivative of the slice functional `J θ = f θ ^ 2 / sin(2θ)`:
with `s = sin(2θ)` and `Φ` the boundary function of `slice_second_defs`, `J' = 2Φ/s^{1-η}`.

Indeed, unfolding `Φ θ = s^{-η} f f' - cos(2θ) s^{-(1+η)} f²`, the right-hand side is
`2 f f' s^{-1} - 2 cos(2θ) f² s^{-2}`, which is the quotient rule for `f²/s`. -/
theorem hasDerivAt_J {f : ℝ → ℝ} {θ : ℝ} (hs : 0 < Real.sin (2 * θ))
    (hd1 : HasDerivAt f (deriv f θ) θ) (hd2 : HasDerivAt (deriv f) (deriv (deriv f) θ) θ) :
    HasDerivAt (fun t : ℝ => (f t) ^ 2 / Real.sin (2 * t))
      (2 * Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi f θ
        / (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)) θ := by
  -- derivative of `t ↦ f t ^ 2`
  have hf2 : HasDerivAt (fun t : ℝ => (f t) ^ 2) (2 * f θ * deriv f θ) θ := by
    have h := hd1.pow 2
    convert h using 1
    norm_num
  -- derivative of `t ↦ sin (2 * t)`
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h2t : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (2 * θ)).comp θ h2t
  have hJ := hf2.div hsin (ne_of_gt hs)
  -- the reduction of the negative powers of `sin (2θ)` to a division by `sin (2θ)`
  have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) =
      (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) / Real.sin (2 * θ) := by
    rw [show -(Work.Spaces.eta) = (1 - Work.Spaces.eta) - 1 by ring,
      Real.rpow_sub hs (1 - Work.Spaces.eta) 1, Real.rpow_one]
  have h2 : (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) =
      (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) / (Real.sin (2 * θ)) ^ 2 := by
    rw [show -(1 + Work.Spaces.eta) = (1 - Work.Spaces.eta) - 2 by ring,
      Real.rpow_sub hs (1 - Work.Spaces.eta) 2]
    simp
  have hval : (2 * f θ * deriv f θ * Real.sin (2 * θ)
        - (f θ) ^ 2 * (2 * Real.cos (2 * θ)))
        / (Real.sin (2 * θ)) ^ 2
      = 2 * Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi f θ
        / (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) := by
    rw [Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi]
    unfold Work.FTS.EllipticEst.Cores.AeStep2Aux.sig Work.FTS.EllipticEst.Cores.AeStep2Aux.sig1
    rw [h1, h2]
    have hA : (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hs _)
    have hs2 : (Real.sin (2 * θ)) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hs)
    field_simp
  exact hJ.congr_deriv hval

end Work.FTS.EllipticEst.Cores.AeStep2Aux.SliceLeftAux
