import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AeStepOneAux.HardyBddDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeStepOneAux.HardyBdd

/-- The flux `hbPrim f θ = 2·hbA·cos(2θ)·(f θ)²·sin(2θ)^{-(1+η)}` of the weighted Hardy
inequality (see `Submission/Work/FTS/EllipticEst/AeStepOneAux/HardyBddDefs.lean`, where `hbA` and
`hbDeriv` are also defined) has, at every interior point `θ ∈ (0, π/2)`, the explicit derivative
`hbDeriv f θ`.  Only `ContDiffOn ℝ 1 f (Ioo 0 (π/2))` (no closed-interval smoothness, no
integrability) is assumed. -/
theorem primDeriv {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (hbPrim f) (hbDeriv f θ) θ := by
  intro θ hθ
  -- `sin (2θ) > 0` on the open quadrant, so all the `rpow`s are differentiable
  have hs2pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs2pos
  -- `f` is differentiable at `θ` with derivative `deriv f θ`
  have hfd : HasDerivAt f (deriv f θ) θ :=
    (hf.differentiableOn one_ne_zero).hasDerivAt (isOpen_Ioo.mem_nhds hθ)
  -- `θ ↦ 2θ`
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 θ := by
    simpa using (hasDerivAt_id' θ).const_mul (2 : ℝ)
  -- `θ ↦ cos (2θ)`
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (2 * y)) (-Real.sin (2 * θ) * 2) θ := by
    simpa using hlin.cos
  -- `θ ↦ sin (2θ)`
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (2 * y)) (Real.cos (2 * θ) * 2) θ := by
    simpa using hlin.sin
  -- `θ ↦ 2·hbA·cos (2θ)`
  have hA : HasDerivAt (fun y : ℝ => 2 * hbA * Real.cos (2 * y))
      (2 * hbA * (-Real.sin (2 * θ) * 2)) θ := by
    simpa using hcos.const_mul (2 * hbA)
  -- `θ ↦ (f θ)²`
  have hfpow : HasDerivAt (fun y : ℝ => (f y) ^ 2) (2 * f θ * deriv f θ) θ := by
    have h := hfd.pow 2
    have hder : (2 * f θ ^ ((2 : ℕ) - 1) * deriv f θ) = (2 * f θ * deriv f θ) := by
      have h1 : ((2 : ℕ) - 1) = 1 := by norm_num
      rw [h1, pow_one]
    exact h.congr_deriv hder
  -- `θ ↦ sin (2θ)^{-(1+η)}`
  have hpow : HasDerivAt (fun y : ℝ => (Real.sin (2 * y)) ^ (-(1 + Work.Spaces.eta)))
      ((Real.cos (2 * θ) * 2) * (-(1 + Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) θ := by
    have h := hsin.rpow_const (p := -(1 + Work.Spaces.eta)) (Or.inl hsne)
    have h2 : ((-(1 + Work.Spaces.eta)) - 1) = (-(2 + Work.Spaces.eta)) := by ring
    simpa only [h2] using h
  -- unfold the flux, keeping the derivative `hbDeriv f θ` as given
  change HasDerivAt (fun y : ℝ => 2 * hbA * Real.cos (2 * y) * (f y) ^ 2
      * (Real.sin (2 * y)) ^ (-(1 + Work.Spaces.eta))) (hbDeriv f θ) θ
  have hmain : HasDerivAt (fun y : ℝ => 2 * hbA * Real.cos (2 * y) * (f y) ^ 2
      * (Real.sin (2 * y)) ^ (-(1 + Work.Spaces.eta))) _ θ :=
    (hA.mul hfpow).mul hpow
  refine hmain.congr_deriv ?_
  simp only [hbDeriv, Pi.mul_apply]
  ring

end Work.FTS.EllipticEst.AeStepOneAux.HardyBdd
