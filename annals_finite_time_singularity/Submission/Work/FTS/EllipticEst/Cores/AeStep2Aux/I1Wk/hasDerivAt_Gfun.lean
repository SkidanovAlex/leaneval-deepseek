import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.SliceThetaIbpDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

/-- **The total-derivative identity underlying the θ-slice IBP.**
`Gfun v ψ θ = ψ θ · (σ θ · v θ · v' θ - η · (cos 2θ · σ₁ θ) · v θ²) - (1/2) · ψ' θ · σ θ · v θ²`
(see `SliceThetaIbpDefs`) is a boundary primitive for the slice identity `S2`: for
`v ∈ C²((0,π/2))`, `ψ ∈ C²(ℝ)` and `θ ∈ (0,π/2)` its derivative is the difference
`Lfun v ψ θ - RHSfun v ψ θ` of the two integrands of `sliceThetaIbpSep`.

Proof route (already prepared in `SliceThetaIbpDefs`): build the product-rule chain
`hσ := sst_hasDerivAt_sig hθ` (`(σ)' = -2η cos2θ σ₁`), `hsigc := hasDerivAt_sigc hθ`
(`(cos2θ σ₁)' = -2σ - 2(1+η)cos²2θ σ₂`), `sst_hasDerivAt_sig1` (`(σ₁)'`), the `HasDerivAt`s of
`v`, `deriv v` (`hv.contDiffAt`), `ψ`, `deriv ψ` (from `hψ : ContDiff ℝ 2 ψ`, e.g. via
`ContDiffOn.deriv_of_isOpen` on `Set.univ` and `DifferentiableOn.differentiableAt`), apply
`HasDerivAt.mul`, `.sub`, `.const_mul`, `.pow`, and finish with `convert h using 1` followed by
`rw [Rawk_eq v ψ hθ]; simp only [sigc]; ring` — the chain's derivative is exactly
`Rawk v ψ θ`, and `Rawk_eq : Rawk v ψ θ = Lfun v ψ θ - RHSfun v ψ θ` is already proved. -/
theorem hasDerivAt_Gfun (v ψ : ℝ → ℝ)
    (hv : ContDiffOn ℝ 2 v (Set.Ioo 0 (Real.pi / 2)))
    (hψ : ContDiff ℝ 2 ψ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Gfun v ψ)
      (Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.Lfun v ψ θ
        - Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.RHSfun v ψ θ) θ := by
  -- differentiability data: `v`, `v'` from `hv`; `ψ`, `ψ'` from `hψ`
  have hv1 : HasDerivAt v (deriv v θ) θ :=
    ((hv.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  have hdv : ContDiffOn ℝ 1 (deriv v) (Set.Ioo 0 (Real.pi / 2)) :=
    hv.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hv2 : HasDerivAt (deriv v) (deriv (deriv v) θ) θ :=
    ((hdv.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  have hψ1 : HasDerivAt ψ (deriv ψ θ) θ :=
    (hψ.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hdψ : ContDiffOn ℝ 1 (deriv ψ) Set.univ :=
    hψ.contDiffOn.deriv_of_isOpen isOpen_univ (m := 1) (by norm_num)
  have hψ2 : HasDerivAt (deriv ψ) (deriv (deriv ψ) θ) θ :=
    ((hdψ.differentiableOn (by norm_num)).differentiableAt
      (isOpen_univ.mem_nhds (Set.mem_univ θ))).hasDerivAt
  -- the derivative of the bracket `σ (v v') - η (c σ₁) v²`
  have hA : HasDerivAt
      (fun t => sig t * (v t * deriv v t) - Work.Spaces.eta * (sigc t * (v t) ^ 2))
      ((-2 * Work.Spaces.eta * Real.cos (2 * θ) * sig1 θ) * (v θ * deriv v θ)
        + sig θ * (deriv v θ * deriv v θ + v θ * deriv (deriv v) θ)
        - Work.Spaces.eta * ((-2 * sig θ - 2 * (1 + Work.Spaces.eta)
              * (Real.cos (2 * θ)) ^ 2 * sig2 θ) * (v θ) ^ 2
            + sigc θ * (2 * v θ ^ (2 - 1) * deriv v θ))) θ :=
    ((sst_hasDerivAt_sig hθ).mul (hv1.mul hv2)).sub
      (((hasDerivAt_sigc hθ).mul (hv1.pow 2)).const_mul Work.Spaces.eta)
  -- the derivative of the second summand `ψ' (σ v²)`
  have hB : HasDerivAt (fun t => deriv ψ t * (sig t * (v t) ^ 2))
      (deriv (deriv ψ) θ * (sig θ * (v θ) ^ 2)
        + deriv ψ θ * ((-2 * Work.Spaces.eta * Real.cos (2 * θ) * sig1 θ) * (v θ) ^ 2
            + sig θ * (2 * v θ ^ (2 - 1) * deriv v θ))) θ :=
    hψ2.mul ((sst_hasDerivAt_sig hθ).mul (hv1.pow 2))
  have hmain := (hψ1.mul hA).sub (hB.const_mul (1 / 2))
  -- the chain's derivative is `Rawk`, which equals `Lfun - RHSfun`
  refine hmain.congr_deriv ?_
  rw [← Rawk_eq v ψ hθ]
  unfold Rawk Lfun
  simp only [sigc]
  ring_nf

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
