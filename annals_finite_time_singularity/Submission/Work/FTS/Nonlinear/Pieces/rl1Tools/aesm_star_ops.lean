/-
# `aesm_star_ops` — a.e. strong measurability of the three `Φ̃_*`-coefficients

The statement asks for the `QdMeas`-a.e.-strong-measurability of the three operators
`ℛ(Φ̃_*)`, `𝒰(Φ̃_*)`, `𝒱(Φ̃_*)` evaluated on the elliptic residual
`Φ̃_* = Φ_* - Θ_*(α)` of the `F_*`-half of the profile, where
`Φ̃_* = Work.FTS.Nonlin.PhiTs α Φs = Φs - Θ α (F_*)`.

The proof is the standard two-step reduction, and everything it needs is already in the
neighbourhood:

* `QdMeas` is `volume ↾ (0,∞) ⊗ volume ↾ Iθ`, and the boundary lines `θ = 0`, `θ = π/2`
  are null, so a function *continuous on the open quadrant* is a.e. strongly measurable
  (`aesm_of_contOn_Qd` of `QuadMeasAux`, whose statement is `SmoothQuad ⟹ a.e. strongly
  measurable` via `aesm_of_smoothQuad`);
* `SmoothQuad` (= genuine `C^∞` on `Ioi (-1) ×ˢ Ioo 0 (π/2)`) is preserved by each of the
  three rational expressions, with the only point of care being the division by
  `cos θ ≠ 0` in `ℛ` and by `cos θ` in `tan θ = sin θ / cos θ` in `𝒱`
  (`smoothQuad_ops` of `blockMeas`, same namespace);
* finally `Φ̃_* = Φs - Θ_*(α)` is `SmoothQuad` because both summands are, and the second
  one is exactly the hypothesis `hΘ` of the statement (this is why the statement carries
  `hΘ` rather than deriving it from `L₁₂(F_*) = 2α/(1+z)`, and hence needs nothing about
  `α`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.QuadMeasAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.blockMeas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option autoImplicit false

/-- The elliptic residual `Φ̃_* = Φ_* - Θ_*(α)` of the `F_*`-half is `C^∞` on the open
quadrant as soon as its two summands are — here `Θ_*(α) = Θ α (F_*)` is the hypothesis
`hΘ` of the statement, so no hypothesis on `α` is needed. -/
theorem smoothQuad_PhiTs_of {α : ℝ} {Φs : ℝ → ℝ → ℝ}
    (hΦs : Work.FTS.LocData.SmoothQuad Φs)
    (hΘ : Work.FTS.LocData.SmoothQuad (Work.Construction.Theta α (Work.Construction.Fstar α))) :
    Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) := by
  change Work.FTS.LocData.SmoothQuad
    (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
  exact Work.FTS.LocData.smoothQuad_sub hΦs hΘ

theorem aesm_star_ops {α : ℝ} {Φs : ℝ → ℝ → ℝ}
    (hΦs : Work.FTS.LocData.SmoothQuad Φs)
    (hΘ : Work.FTS.LocData.SmoothQuad (Work.Construction.Theta α (Work.Construction.Fstar α))) :
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)))
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas ∧
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)))
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas ∧
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)))
      Work.FTS.Nonlinear.Pieces.rl1Tools.QdMeas := by
  have hPhiTs : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) :=
    smoothQuad_PhiTs_of hΦs hΘ
  obtain ⟨hR, hU, hV⟩ := smoothQuad_ops (α := α) (Ψ := Work.FTS.Nonlin.PhiTs α Φs) hPhiTs
  exact ⟨aesm_of_smoothQuad hR, aesm_of_smoothQuad hU, aesm_of_smoothQuad hV⟩

end Work.FTS.Nonlinear.Pieces.rl1Tools
