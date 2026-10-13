/-
Copyright: work module for the Elgindi finite-time singularity project.

# The derivative of the angular weight `sigE` on the open interval

This module proves that the angular weight `sigE η θ = sin(2θ)^{-η}` of
`Work.FTS.EllipticEst.AngSecond.slice_ibp_sigma` is differentiable on the open interval
`(0, π/2)`, with derivative the function `sigD η θ = -2η cos(2θ) sin(2θ)^{-(1+η)}`
declared in `SliceIBPDefs`.  This is the pointwise ingredient turning `sigD` into the
honest derivative of `sigE`, needed to run the one-dimensional integration by parts in
`θ` (`slice_ibp_sigma`, `slice_second_deriv_eq`).

The proof is the chain rule for the real power `x ↦ x ^ (-η)`: on `(0, π/2)` the base
`θ ↦ sin(2θ)` is strictly positive (`sin_pos_of_pos_of_lt_pi` applied to `2θ ∈ (0, π)`),
so `HasDerivAt.rpow_const` applies with the base differentiability
`d/dθ sin(2θ) = 2 cos(2θ)`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AngSecond.SliceIBPDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngSecond

theorem sigE_hasDerivAt (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => Work.FTS.EllipticEst.AngSecond.sigE η t)
      (Work.FTS.EllipticEst.AngSecond.sigD η θ) θ := by
  -- the base `sin(2θ)` is strictly positive strictly inside the interval
  have hsin_pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  -- `d/dθ sin(2θ) = 2 cos(2θ)`
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
    hlin.sin
  -- the chain rule for the real power `x ↦ x ^ (-η)`
  have hpow := hsin.rpow_const (p := -η) (Or.inl (ne_of_gt hsin_pos))
  -- identify the chain-rule derivative with `sigD η θ`
  have hval : (Real.cos (2 * θ) * 2) * (-η) * Real.sin (2 * θ) ^ (-η - 1)
      = Work.FTS.EllipticEst.AngSecond.sigD η θ := by
    rw [Work.FTS.EllipticEst.AngSecond.sigD_apply]
    have h_exp : -η - 1 = -(1 + η) := by ring
    rw [h_exp]
    ring
  exact hpow.congr_deriv hval

end Work.FTS.EllipticEst.AngSecond
