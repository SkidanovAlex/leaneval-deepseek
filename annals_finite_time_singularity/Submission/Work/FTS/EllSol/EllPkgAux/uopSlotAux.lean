/-
# `Work.FTS.EllSol.EllPkgAux.uopSlotAux` — a helper for the `U/sin 2θ`-slot at level `4`

This module carries the local helper of `Work.FTS.EllSol.EllPkgAux.uopSlotLe4` that is not part
of the shared library:

* `smoothOpen_radial_slot` — `SmoothOpen` of a radial function `(z,θ) ↦ Λ z`.

The reduction identity on the open quadrant,

  `Uop α Ξ / sin 2θ = -3(X/σ) - α(D_zX/σ) - (2Ḡ + (3/4)F_*)`,  `Ξ = EllResid α g Ψ`,
  `X = ellShift α g Ψ`,

is imported from its own module `FTS/EllSol/EllPkgAux/uopPointwiseId`
(`Work.FTS.EllSol.EllPkgAux.uopPointwiseId`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllExist.SmoothOpenSep
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllSol.EllPkgAux.uopPointwiseId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- `SmoothOpen` of a radial function `(z,θ) ↦ Λ z`, for a profile smooth on `(0,∞)`. -/
theorem smoothOpen_radial_slot {Λ : ℝ → ℝ}
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Λ z) := by
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllExist.sep_mul_open (g := Λ) (χ := fun _ : ℝ => (1 : ℝ)) hΛ
      contDiff_const) fun z θ _ _ _ => by ring

end Work.FTS.EllSol.EllPkgAux
