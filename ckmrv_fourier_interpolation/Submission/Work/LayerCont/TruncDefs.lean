/-
# The trunc part of the continuation of the CKMRV layer across `Re τ = 1`

The mirror of `Submission/Work/LayerCont/Defs.lean` (`layerLowPiece`, `layerLowCont`) for the
*trunc* piece `[1,∞)` of the layer: when the pole `z = τ - 1` of the kernel crosses the contour at
height `t₀ = Im τ > 1`, it meets the truncated range `[1,∞)` rather than the low range `(0,1]`.

The two definitions here are the objects of `Work.LayerCont.TruncAgreement`:
`Work.LayerCont.layerTruncCont ℓ d t₀ A ξ r τ = Work.Asymptotics.layerTrunc (Gcusp ℓ d) ℓ d τ r`
on `{Re τ < 1}` inside the ball (see `Work.LayerCont.TruncAgreement`).

Note the two `Aexp`-terms: `layerTruncPiece` subtracts the entire cusp model `Aexp` on the retained
part of `[1,∞)`, and the *third* term subtracts `∫_I Aexp·gaussWeight` over the removed interval
`I = (t₀-A, t₀+A)`: this is the detour of the `Aexp` part, which is exact because `Aexp (Gcusp ℓ d)`
is entire in `z` (so its contour integral over the closed rectangle vanishes).  Without it the
identity with `layerTrunc` is false (the sweep of `I` by the detour would drop the `Aexp`
contribution of `I`), which is precisely what the review of the first (wrong) statement caught.
-/
import Mathlib
import Submission.Work.LayerCont.Defs
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory

/-- The truncated part of the contour `[1,∞)` with the interval `(t₀-A, t₀+A)` (the one swept by the
moving pole `τ - 1` when `Im τ` is near `t₀ > 1`) removed, with the cusp model `Aexp` subtracted so
that the integrand decays. -/
def layerTruncPiece (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (t₀ A r : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  ∫ t in Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A) (t₀ + A),
    (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
      * Work.Asymptotics.gaussWeight r t

/-- **The continuation of `layerTrunc` across `Re τ = 1`.**  The integral over the deformed contour
(the removed interval `(t₀-A, t₀+A)` replaced by the left detour at height `t₀`), minus the `Aexp`
detour over the removed interval, plus the residue correction `e^{iπr²(τ-1)}`. -/
def layerTruncCont (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (t₀ A ξ r : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  Work.Asymptotics.sinSqC r
      * (layerTruncPiece ℓ d t₀ A r τ + Work.Asymptotics.detourLeftC ℓ d r t₀ A ξ τ
          - ∫ t in Set.Ioo (t₀ - A) (t₀ + A),
              Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
                * Work.Asymptotics.gaussWeight r t)
    + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ

end Work.LayerCont
