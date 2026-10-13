/-
Copyright: work module for the Elgindi finite-time singularity project.

# Derivative of the Hardy flux `Φ θ = f θ² cos(2θ) sin(2θ)^{-(1+η)}`

For `f : ℝ → ℝ` of class `C²` on the open interval `(0, π/2)` and every
`θ ∈ (0, π/2)`,

  `Φ' θ = 2 G θ - 2 B θ - 2 (1+η) L θ`

where (see `Submission/Work/FTS/EllipticEst/AngAWeakFts/Defs.lean`)

* `G θ = f' θ · f θ · cos(2θ) · sin(2θ)^{-(1+η)}`,
* `B θ = f θ² · sin(2θ)^{-η}`,
* `L θ = f θ² · cos²(2θ) · sin(2θ)^{-(2+η)}`.

The only rpow algebra needed is `sin(2θ)^{-η} = sin(2θ) · sin(2θ)^{-(1+η)}`,
which is `Real.rpow_add` at the positive point `sin(2θ)`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AngAWeakFts.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeakFts

open Work.FTS.EllipticEst.AngAWeak

/-- The flux `Φ` has derivative `2G - 2B - 2(1+η)L` on the open angular interval. -/
theorem fluxDeriv (η : ℝ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      HasDerivAt (Work.FTS.EllipticEst.AngAWeak.hardyFtsFlux η f)
        (2 * Work.FTS.EllipticEst.AngAWeak.hardyFtsG η f θ
          - 2 * Work.FTS.EllipticEst.AngAWeak.hardyFtsB η f θ
          - 2 * (1 + η) * Work.FTS.EllipticEst.AngAWeak.hardyFtsL η f θ) θ := by
  intro θ hθ
  have hsin : 0 < Real.sin (2 * θ) := hardyFts_sin_pos hθ
  -- `f` is differentiable at the interior point `θ`
  have hf_diff : DifferentiableAt ℝ f θ :=
    (hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
  have hfd : HasDerivAt f (deriv f θ) θ := hf_diff.hasDerivAt
  -- the two trigonometric chains
  have hsin2 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  have hcos2 : HasDerivAt (fun θ : ℝ => Real.cos (2 * θ)) (-2 * Real.sin (2 * θ)) θ := by
    simpa [Function.comp_def, mul_comm, mul_neg] using
      (Real.hasDerivAt_cos (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
  -- the three factors of the flux and their derivatives
  have hA := hfd.pow 2
  have hC : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) ^ (-(1 + η)))
      ((2 * Real.cos (2 * θ)) * (-(1 + η)) * Real.sin (2 * θ) ^ (-(1 + η) - 1)) θ :=
    hsin2.rpow_const (Or.inl hsin.ne')
  have hD := (hA.mul hcos2).mul hC
  -- the two `rpow` rewrites identifying the terms of the target
  have hsub : Real.sin (2 * θ) ^ (-η) = Real.sin (2 * θ) * Real.sin (2 * θ) ^ (-(1 + η)) := by
    rw [show (-η : ℝ) = 1 + (-(1 + η)) by ring, Real.rpow_add hsin, Real.rpow_one]
  have hsub2 : Real.sin (2 * θ) ^ (-(2 + η)) = Real.sin (2 * θ) ^ (-(1 + η) - 1) := by
    rw [show (-(2 + η) : ℝ) = -(1 + η) - 1 by ring]
  refine hD.congr_deriv ?_
  unfold hardyFtsG hardyFtsB hardyFtsL
  rw [hsub, hsub2]
  simp only [Pi.mul_apply, Pi.pow_apply]
  ring

end Work.FTS.EllipticEst.AngAWeakFts
