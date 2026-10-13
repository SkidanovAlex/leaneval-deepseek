/-
# The CONSTRUCTION area: the self-similar ansatz and the stationary equations (tex 1330-1332)

The ansatz of §Modulation is

  `Ω(R,θ,t) = (1-(1+μ)t)^{-1} F(R/(1-(1+μ)t)^{1+λ}, θ)`,  `Ψ = (1-(1+μ)t)^{-1}Φ(z,θ)`,
  `z = R/(1-(1+μ)t)^{1+λ}`,

and the self-similar vorticity equation `\eqref{OmegaEvolutionFinal}` reads

  `(1/2)∂_tΩ + U(Ψ)∂_θΩ + V(Ψ)αR∂_RΩ = ℛ(Ψ)Ω`.

Substituting the ansatz (using the chain rule for `∂_t`, proved in
`Submission/Work/Construction/hasDerivAt_OmegaAns.lean`; `∂_θΩ = (1-(1+μ)t)^{-1}∂_θF`,
`R∂_RΩ = z∂_zF`, and similarly for `Ψ`) turns the vorticity equation into

  `(1-(1+μ)t)^{-2}·(1/2)·[ (1+μ)F + (1+μ)(1+λ)z∂_zF + 2U(Φ)∂_θF + 2αV(Φ)z∂_zF - 2ℛ(Φ)F ] = 0`,

i.e. — by the very definition of `StatEqF` (`UVR` collects the last three terms) — into the
*stationary equation for `F`* `StatEqF α μ lam F Φ`.  That equivalence, after the chain rule, is
pure algebra, and it is what `vorticity_reduces` records:

* every term of the vorticity equation is `(1-(1+μ)t)^{-2}` times the corresponding term of
  `StatEqF`, because `U(Ψ)`, `V(Ψ)`, `ℛ(Ψ)` are all `(1-(1+μ)t)^{-1}` times `U(Φ)`, `V(Φ)`,
  `ℛ(Φ)` (they are linear in `Ψ`, and `R∂_RΨ = z∂_zΦ`).

The paper's equation `\eqref{PolarBSLFinal}` for `Φ` is the definition `StatEqPhi`
(`Work.Elliptic.bslOp α Φ = F`): it is already written in the self-similar variables and needs
no chain rule.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Construction.Defs
import Submission.Work.Construction.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Construction

set_option autoImplicit false

/-- **The vorticity equation for the ansatz reduces to `StatEqF`.**  Let `u = 1-(1+μ)t > 0`,
`z = R/u^{1+λ}`.  Substituting the ansatz into `\eqref{OmegaEvolutionFinal}` gives
`u^{-2}·(1/2)·[(1+μ)F + (1+μ)(1+λ)z∂_zF + UVR(F,Φ)]` (this is where the chain rule
`hasDerivAt_OmegaAns`/`hasDerivAt_zvar` is used), so the vorticity equation holds at `(z,θ)` as
soon as `F, Φ` satisfy the stationary equation `StatEqF`. -/
theorem vorticity_reduces {α μ lam : ℝ} (hα : 0 < α) {F Φ : ℝ → ℝ → ℝ} {z θ t : ℝ}
    (hu : (0 : ℝ) < 1 - (1 + μ) * t) (hstat : StatEqF α μ lam F Φ) :
    (1 / 2) * ((1 + μ) * (1 - (1 + μ) * t) ^ (-2 : ℝ)
        * (F z θ + (1 + lam) * Work.Spaces.Dz F z θ))
      + (1 - (1 + μ) * t) ^ (-2 : ℝ) * (Uop α Φ z θ * Work.Spaces.pth F z θ
        + α * Vop Φ z θ * Work.Spaces.Dz F z θ - Rop α Φ z θ * F z θ) = 0 := by
  have h := hstat z θ
  have key : (1 + μ) * F z θ + (1 + μ) * (1 + lam) * Work.Spaces.Dz F z θ
      + (2 * Uop α Φ z θ * Work.Spaces.pth F z θ
        + 2 * α * Vop Φ z θ * Work.Spaces.Dz F z θ
        - 2 * Rop α Φ z θ * F z θ) = 0 := by
    rw [← h]
    simp only [UVR]
    try ring
  have hgoal : (1 / 2) * ((1 + μ) * (1 - (1 + μ) * t) ^ (-2 : ℝ)
        * (F z θ + (1 + lam) * Work.Spaces.Dz F z θ))
      + (1 - (1 + μ) * t) ^ (-2 : ℝ) * (Uop α Φ z θ * Work.Spaces.pth F z θ
        + α * Vop Φ z θ * Work.Spaces.Dz F z θ - Rop α Φ z θ * F z θ)
      = (1 / 2) * (1 - (1 + μ) * t) ^ (-2 : ℝ) * ((1 + μ) * F z θ
        + (1 + μ) * (1 + lam) * Work.Spaces.Dz F z θ
        + (2 * Uop α Φ z θ * Work.Spaces.pth F z θ
          + 2 * α * Vop Φ z θ * Work.Spaces.Dz F z θ
          - 2 * Rop α Φ z θ * F z θ)) := by ring
  rw [hgoal, key, mul_zero]

end Work.Construction
