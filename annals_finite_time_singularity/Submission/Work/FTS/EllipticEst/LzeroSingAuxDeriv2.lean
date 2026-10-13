/-
Work module for the Elgindi finite-time singularity project.

# Derivative of `SingY1` (self-contained)

`SingY1 θ = 2 cos(2θ)·SingInt θ - 1/(cos θ · sin 2θ)`; its derivative is
`SingY2 θ = -4 sin(2θ)·SingInt θ - sin θ/(cos²θ · sin 2θ)`.

The computation: the product rule with `SingInt' = -LzeroSingIntegrand (π/2 - ·)`, the quotient
rule for `1/(cos θ sin 2θ)`, the evaluation `LzeroSingIntegrand (π/2 - θ) = 1/(cos θ · sin²2θ)`,
and the algebraic simplification `y2_value_identity`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.LzeroSingAuxDefs
import Submission.Work.FTS.EllipticEst.LzeroSingAuxDeriv
import Submission.Work.FTS.EllipticEst.LzeroAux.y2_value_identity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

theorem LzeroSingIntegrand_pi_div_two_sub (θ : ℝ) :
    LzeroSingIntegrand (Real.pi / 2 - θ) = 1 / (Real.cos θ * Real.sin (2 * θ) ^ 2) := by
  have h1 : Real.sin (Real.pi / 2 - θ) = Real.cos θ := Real.sin_pi_div_two_sub θ
  have h2 : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
    rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
  simp only [LzeroSingIntegrand, h1, h2]

theorem SingY1_hasDerivAt_self : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    HasDerivAt SingY1 (SingY2 θ) θ := by
  intro θ hθ
  have hθπ : θ < Real.pi / 2 := hθ.2
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθπ⟩
  have hcos_ne : Real.cos θ ≠ 0 := ne_of_gt hcos_pos
  have hsin2_ne : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθπ]⟩)
  have hlin : HasDerivAt (fun t : ℝ => (2 : ℝ) * t) 2 θ := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id θ).const_mul 2
  have hsin2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ :=
    ((Real.hasDerivAt_sin (2 * θ)).comp θ hlin).congr_deriv (by ring)
  have hcos2 : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-(2 * Real.sin (2 * θ))) θ :=
    ((Real.hasDerivAt_cos (2 * θ)).comp θ hlin).congr_deriv (by ring)
  have hint : HasDerivAt SingInt (-(LzeroSingIntegrand (Real.pi / 2 - θ))) θ :=
    SingInt_hasDerivAt θ hθ
  -- first summand `2 cos(2·) · SingInt`
  have hg1 : HasDerivAt (fun t : ℝ => (2 : ℝ) * Real.cos (2 * t))
      (2 * (-(2 * Real.sin (2 * θ)))) θ := hcos2.const_mul 2
  have h1 : HasDerivAt (fun t : ℝ => 2 * Real.cos (2 * t) * SingInt t)
      (2 * (-(2 * Real.sin (2 * θ))) * SingInt θ
        + 2 * Real.cos (2 * θ) * (-(LzeroSingIntegrand (Real.pi / 2 - θ)))) θ :=
    hg1.mul hint
  -- second summand `1/(cos · sin 2·)`
  have hp : HasDerivAt (fun t : ℝ => Real.cos t * Real.sin (2 * t))
      (2 * Real.cos θ * Real.cos (2 * θ) - Real.sin θ * Real.sin (2 * θ)) θ :=
    ((Real.hasDerivAt_cos θ).mul hsin2).congr_deriv (by ring)
  have h2 : HasDerivAt (fun t : ℝ => 1 / (Real.cos t * Real.sin (2 * t)))
      (-(2 * Real.cos θ * Real.cos (2 * θ) - Real.sin θ * Real.sin (2 * θ))
        / (Real.cos θ * Real.sin (2 * θ)) ^ 2) θ := by
    have h := hp.inv (mul_ne_zero hcos_ne hsin2_ne)
    convert h using 1
    funext t
    simp only [Pi.inv_apply, one_div]
  have h12 := h1.sub h2
  have hval : 2 * (-(2 * Real.sin (2 * θ))) * SingInt θ
        + 2 * Real.cos (2 * θ) * (-(LzeroSingIntegrand (Real.pi / 2 - θ)))
        - (-(2 * Real.cos θ * Real.cos (2 * θ) - Real.sin θ * Real.sin (2 * θ))
            / (Real.cos θ * Real.sin (2 * θ)) ^ 2) = SingY2 θ := by
    rw [LzeroSingIntegrand_pi_div_two_sub θ, SingY2_apply]
    rw [← LzeroAux.y2_value_identity θ hθ (SingInt θ)]
    ring
  exact h12.congr_deriv hval

end Work.FTS.EllipticEst
