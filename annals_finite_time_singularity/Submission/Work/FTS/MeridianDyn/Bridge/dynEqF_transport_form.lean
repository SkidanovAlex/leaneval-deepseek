import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.LinearCombination
import Submission.Work.Construction.Equation
import Submission.Work.Construction.Basic
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge

/-- **The transport form of the profile equation.**  Writing `Φ = Φ̃ + Θ` with
`Θ = (1/(4α)) sin(2θ) L₁₂(F)` (hypotheses `h1`--`h3`, `h5`; `h4`/`h6` are definitional), the
quadratic form `UVR α F Φ = 2U(Φ)∂_θF + 2αV(Φ)D_zF - 2ℛ(Φ)F` can be put in the *transport
form* whose coefficients involve only `Φ̃ = Φ - Θ` and the two angular moments `L₁₂(F)`,
`(F,K)_{L²_θ}` of `F`:

`(1+μ)F + (1-μ)D_zF + UVR(F,Φ)`
` = ((1-μ) + L₁₂(F)·c2m(θ) + 2αV(Φ̃))·D_zF + 2U(Φ)·∂_θF`
`   + ((1+μ) - L₁₂(F)/α + sin²θ (F,K) - 2ℛ(Φ̃))·F`.

This is the pointwise algebraic core of `Work.FTS.Galerkin.IsDynEqOn` (the `∂_τF + …` display):
the `U`-slot keeps the *full* `Φ` — its `Θ`-part `2U(Θ) = -(3/(2α))sin(2θ)L₁₂(F) + (1/2)sin(2θ)(F,K)`
supplies exactly the two `∂_θF`-terms that `UVR_sub` produces — while the `V`- and `ℛ`-slots are
evaluated at the regular part `Φ̃`, with the corrections `L₁₂(F)c2m(θ)` resp.
`-L₁₂(F)/α + sin²θ(F,K)`.

Proof: `Construction.UVR_sub` (the substitution `Φ = Φ̃ + Θ`) plus the affineness of `U` in its
argument and the two evaluations of `U`/`V`/`ℛ` at `Θ`. -/
theorem dynEqF_transport_form {α μ : ℝ} (hα : 0 < α)
    {F Φ : ℝ → ℝ → ℝ} (z θ : ℝ) (hcos : Real.cos θ ≠ 0)
    (h1 : Φ z θ = Work.Construction.PhiTil α F Φ z θ + Work.Construction.Theta α F z θ)
    (h2 : Work.Spaces.pz Φ z θ = Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z θ
      + Work.Spaces.pz (Work.Construction.Theta α F) z θ)
    (h3 : Work.Spaces.pth Φ z θ = Work.Spaces.pth (Work.Construction.PhiTil α F Φ) z θ
      + Work.Spaces.pth (Work.Construction.Theta α F) z θ)
    (h5 : z * Work.Spaces.pz (Work.Construction.Theta α F) z θ
      = -(1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.FK F z) :
    (1 + μ) * F z θ + (1 - μ) * Work.Spaces.Dz F z θ + Work.Construction.UVR α F Φ z θ
      = ((1 - μ) + Work.Construction.L12 F z * Work.Construction.c2m θ
            + 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ)
          * Work.Spaces.Dz F z θ
        + (2 * Work.Construction.Uop α Φ z θ) * Work.Spaces.pth F z θ
        + ((1 + μ) - Work.Construction.L12 F z / α + Real.sin θ ^ 2 * Work.Construction.FK F z
            - 2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ) * F z θ := by
  -- `Θ z θ = (1/(4α)) sin(2θ) L₁₂(F)`: the definitional evaluation of the singular part.
  have h4 : Work.Construction.Theta α F z θ
      = (1 / (4 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z := rfl
  -- `∂_θ Θ = (1/(2α)) cos(2θ) L₁₂(F)`.
  have h6 := Work.Construction.pth_Theta_eq hα (F := F) z θ
  -- **The substitution** `Φ = Φ̃ + Θ`: both the `V`- and the `ℛ`-slot of the quadratic form
  -- pick up the explicit `L₁₂(F)`-corrections, while the `U`-slot is left as `U(Φ̃)`.
  have hsub := Work.Construction.UVR_sub α hα z θ hcos h1 h2 h3 h4 h5 h6
  -- `U` is affine in its argument, so `U(Φ) = U(Φ̃) + U(Θ)` along `Φ = Φ̃ + Θ`.
  have hU : Work.Construction.Uop α Φ z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
        + Work.Construction.Uop α (Work.Construction.Theta α F) z θ := by
    simp only [Work.Construction.Uop]
    rw [h1, h2]
    ring
  -- `2U(Θ) = -(3/(2α)) sin(2θ)L₁₂(F) + (1/2) sin(2θ)(F,K)`: the `U`-slot correction, whose two
  -- pieces are exactly the `∂_θF`-terms of `UVR_sub` (with opposite signs).
  have hUΘ : 2 * Work.Construction.Uop α (Work.Construction.Theta α F) z θ
      = -(3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z
        + (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z := by
    simp only [Work.Construction.Uop]
    rw [h4]
    rw [show α * z * Work.Spaces.pz (Work.Construction.Theta α F) z θ
        = α * (z * Work.Spaces.pz (Work.Construction.Theta α F) z θ) from by ring, h5]
    field_simp
    ring
  -- the `∂_θF`-slot of the target right-hand side: `2U(Φ)∂_θF` is `2U(Φ̃)∂_θF` up to exactly the
  -- two corrections produced by `UVR_sub`.
  have hpt : 2 * Work.Construction.Uop α Φ z θ * Work.Spaces.pth F z θ
      = 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
          * Work.Spaces.pth F z θ
        + (-(3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z
            + (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z)
          * Work.Spaces.pth F z θ := by
    have h2' : 2 * Work.Construction.Uop α Φ z θ
        = 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
          + (-(3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 F z
              + (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z) := by
      rw [hU]
      linear_combination hUΘ
    rw [h2']; ring
  rw [hsub]
  simp only [Work.Construction.UVR]
  rw [hpt]
  ring

end Work.FTS.MeridianDyn.Bridge
