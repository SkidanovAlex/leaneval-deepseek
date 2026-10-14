import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Stability.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- **The static identity for the `g`-equation** (tex 1345 *without* the stationary equation).

For arbitrary `F, Φ` that admit the paper's decomposition `Φ = Φ̃ + Θ` (`Φ̃ = Φ - Θ`,
`Θ = (1/(4α)) sin(2θ)L₁₂(F)`) with the derivative evaluations `h5`, `h6` of `Θ` (supplied by
`Work.Construction.Dz_Theta_eq` / `pth_Theta_eq`), one has

  `(1+μ)F + (1+μ)(1+λ)D_zF + UVR α F Φ = MainLHS α μ lam F - N α F Φ`.

The Construction area's `MainLHS_eq_N` proves `MainLHS = N` *under* the stationary equation
`StatEqF`; the identity above needs no such hypothesis, and it is precisely what the dynamical
(dissipative) equation requires.

Proof route: `Work.Construction.UVR_sub` gives `UVR α F Φ = UVR α F Φ̃ - X + M` with
`X = (1/α)L₁₂(F)F + (3/(2α))sin(2θ)L₁₂(F)∂_θF - c2m(θ)L₁₂(F)D_zF` and
`M = (1/2)sin(2θ)(F,K)∂_θF + sin²θ(F,K)F`, while by definition
`N α F Φ = -UVR α F Φ̃ - M`; so `UVR α F Φ = -X - N α F Φ`.  Since
`MainLHS α μ lam F = (1+μ)F + (1+μ)(1+λ)D_zF - X`, the claim follows by linear arithmetic. -/
theorem MainLHSSubN {α μ lam : ℝ} (hα : 0 < α) {F Φ : F2} (z θ : ℝ) (hcos : Real.cos θ ≠ 0)
    (h1 : Φ z θ = Work.Construction.PhiTil α F Φ z θ + Work.Construction.Theta α F z θ)
    (h2 : Work.Spaces.pz Φ z θ
      = Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z θ
        + Work.Spaces.pz (Work.Construction.Theta α F) z θ)
    (h3 : Work.Spaces.pth Φ z θ
      = Work.Spaces.pth (Work.Construction.PhiTil α F Φ) z θ
        + Work.Spaces.pth (Work.Construction.Theta α F) z θ)
    (h5 : z * Work.Spaces.pz (Work.Construction.Theta α F) z θ
      = -(1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.FK F z)
    (h6 : Work.Spaces.pth (Work.Construction.Theta α F) z θ
      = (1 / (2 * α)) * Real.cos (2 * θ) * Work.Construction.L12 F z) :
    (1 + μ) * F z θ + (1 + μ) * (1 + lam) * Work.Spaces.Dz F z θ
        + Work.Construction.UVR α F Φ z θ
      = Work.Construction.MainLHS α μ lam F z θ - Work.Construction.N α F Φ z θ := by
  have hsub := Work.Construction.UVR_sub α hα (F := F) (Φ := Φ)
    (Φt := Work.Construction.PhiTil α F Φ) (Θ := Work.Construction.Theta α F)
    z θ hcos h1 h2 h3 rfl h5 h6
  rw [hsub]
  simp only [Work.Construction.MainLHS, Work.Construction.N, Work.Construction.UVR,
    Work.Construction.Uop, Work.Construction.Vop, Work.Construction.Rop]
  ring

end Work.Stability
