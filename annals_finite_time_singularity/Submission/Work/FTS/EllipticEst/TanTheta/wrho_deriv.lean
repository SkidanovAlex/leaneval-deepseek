import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.TanTheta.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Filter
open scoped Topology

namespace Work.FTS.EllipticEst.TanTheta

/-- On `(0, π/2)` the weight `ρ = sin θ · cos θ · sin(2θ)^{-η}` equals `(1/2) sin(2θ)^{1-η}`
(using `sin(2θ) = 2 sin θ cos θ` and `Real.rpow_add` at the positive base `sin (2θ)`). -/
theorem wrho_eventuallyEq (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    wrho η =ᶠ[𝓝 θ] fun θ' => (1 / 2) * (Real.sin (2 * θ')) ^ (1 - η) := by
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
  have hpos : 0 < Real.sin (2 * θ') :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ'.1]) (by linarith [hθ'.2])
  show Real.sin θ' * Real.cos θ' * (Real.sin (2 * θ')) ^ (-η)
      = (1 / 2) * (Real.sin (2 * θ')) ^ (1 - η)
  have h1 : Real.sin θ' * Real.cos θ' = Real.sin (2 * θ') / 2 := by
    rw [Real.sin_two_mul]; ring
  have h2 : Real.sin (2 * θ') * (Real.sin (2 * θ')) ^ (-η)
      = (Real.sin (2 * θ')) ^ (1 - η) := by
    have h3 := Real.rpow_add hpos (1 : ℝ) (-η)
    rw [Real.rpow_one, show (1 : ℝ) + -η = 1 - η by ring] at h3
    exact h3.symm
  rw [h1,
    show Real.sin (2 * θ') / 2 * (Real.sin (2 * θ')) ^ (-η)
        = (1 / 2) * (Real.sin (2 * θ') * (Real.sin (2 * θ')) ^ (-η)) by ring,
    h2]

/-- The derivative of the integration weight `ρ θ = sin θ cos θ sin(2θ)^{-η}` on `(0, π/2)`:
`ρ' θ = (1-η) cos(2θ) sin(2θ)^{-η}`.  (Note `sin θ cos θ = sin(2θ)/2`, so on the open interval
`ρ = (1/2) sin(2θ)^{1-η}`, whose derivative is `(1-η) cos(2θ) sin(2θ)^{-η}`; the definition
`wrhoD` in `Submission/Work/FTS/EllipticEst/TanTheta/Basic.lean` matches this.)

Route: `ρ = (1/2) · s^{1-η}` with `s θ = sin(2θ)`, using `Real.rpow_add` at the positive base
`sin (2θ)` (`Work.FTS.H2.sin_two_pos_of_Ioo` in `Submission/Work/FTS/H2/STBasic.lean`, or
`Real.sin_pos_of_pos_of_lt_pi`); then differentiate `s ↦ s^{1-η}` with
`Real.hasDerivAt_rpow_const` and the chain rule with
`HasDerivAt (fun θ => Real.sin (2 θ)) (2 cos (2θ)) θ`, and finish with `Real.rpow_add` and
`ring`. -/
theorem wrho_deriv (η : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Work.FTS.EllipticEst.TanTheta.wrho η)
      (Work.FTS.EllipticEst.TanTheta.wrhoD η θ) θ := by
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := hasDerivAt_const_mul (2 : ℝ)
    exact (HasDerivAt.comp (hh₂ := Real.hasDerivAt_sin (2 * θ)) (hh := h1)).congr_deriv (by ring)
  have hrpow :
      HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ')) ^ (1 - η))
        (2 * Real.cos (2 * θ) * (1 - η) * (Real.sin (2 * θ)) ^ (1 - η - 1)) θ :=
    hsin.rpow_const (p := 1 - η) (Or.inl (ne_of_gt hspos))
  have hval :
      (1 / 2) * (2 * Real.cos (2 * θ) * (1 - η) * (Real.sin (2 * θ)) ^ (1 - η - 1))
        = Work.FTS.EllipticEst.TanTheta.wrhoD η θ := by
    simp only [Work.FTS.EllipticEst.TanTheta.wrhoD]
    rw [show (1 : ℝ) - η - 1 = -η by ring]
    ring
  have hconst :
      HasDerivAt (fun θ' : ℝ => (1 / 2) * (Real.sin (2 * θ')) ^ (1 - η))
        (Work.FTS.EllipticEst.TanTheta.wrhoD η θ) θ :=
    (HasDerivAt.const_mul (1 / 2 : ℝ) hrpow).congr_deriv hval
  exact HasDerivAt.congr_of_eventuallyEq hconst (wrho_eventuallyEq η hθ)

end Work.FTS.EllipticEst.TanTheta
