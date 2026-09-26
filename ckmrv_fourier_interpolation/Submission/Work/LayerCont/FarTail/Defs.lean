/-
# The far-side (`Re τ > 1`) chart nomenclature of the CKMRV layer

This directory (`Work.LayerCont.FarTail`) carries the **far side** of the first recurrence of the
CKMRV layer: everything is about the half-plane `1 < Re τ`, the side on which the pole
`τ - 1` has *positive* real part and the removable coincidence `ST⁻¹τ = -1/(τ-1)` has *negative*
real part (`Work.LayerCont.Coinc.coincℂ_re_neg_iff`).

The window chart of `Work.LayerCont.layerWindowContinuation` is the function

  `layerLowDouble ℓ d p s₀ A₁ ξ₁ A₂ ξ₂ r + layerTruncAt (Gcusp ℓ d) ℓ d p r + highPartAt (Gcusp ℓ d) p r`,

holomorphic on a ball `B(1 + i s₀, ε')` and equal to `paperLayer` on the `𝒟`-side of that ball.
On the far side (`1 < τ.re`) it is equal to `paperLayer (Gcusp ℓ d) ℓ d τ r + sinSqC r * resCorr r τ`
(this is the far-side statement of CKMRV (5.7)); this directory proves that identity and the
resulting recurrence `T2op H = -T2op (gaussTerm · r)`.

Here we only *name* the chart (`windowChart`), so that the statements below can refer to it.
-/
import Mathlib
import Submission.Work.LayerCont.WindowCapstone
import Submission.Work.LayerCont.Coinc.All
import Submission.Work.LayerCont.FirstRecurrence

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.FarTail

open Work.Asymptotics Work.LayerCont

/-- **The window chart of the CKMRV layer continuation** (`p` the split point, `t₀` the height of
the pole rectangle, `Aᵢ, ξᵢ` its half-heights and depths).  This is the function of
`Work.LayerCont.layerWindowContinuation`, packaged under a name. -/
def windowChart (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (p t₀ A₁ ξ₁ A₂ ξ₂ : ℝ) (r : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  Work.LayerCont.layerLowDouble ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ
    + Work.LayerCont.layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
    + Work.LayerCont.highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ

/-- The chart is *definitionally* the sum of the three pieces (used to rewrite between the
unbundled and the bundled spelling). -/
lemma windowChart_eq (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (p t₀ A₁ ξ₁ A₂ ξ₂ : ℝ) (r : ℝ)
    (τ : UpperHalfPlane) :
    windowChart ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ
      = Work.LayerCont.layerLowDouble ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ
        + Work.LayerCont.layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
        + Work.LayerCont.highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ := rfl

/-- **The far-side reading of the chart.**  Once the far-side contour identity
(`Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far`) and the far-side `layerAt = paperLayer`
are available at `τ`, the chart is `paperLayer` plus the residue correction.

This is the `hdef1`-shaped conclusion the first recurrence consumes: the residue correction is
*not* cancelled on the far side, because there the pole `τ - 1` lies to the *right* of the
imaginary axis and so is missed by the left detour. -/
theorem windowChart_eq_paperLayer_add_resCorr
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (p t₀ A₁ ξ₁ A₂ ξ₂ : ℝ) (r : ℝ)
    (τ : UpperHalfPlane)
    (hlow : Work.LayerCont.layerLowDouble ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ
      = Work.LayerCont.layerLowAt ℓ d p r τ + Work.Asymptotics.sinSqC r
          * Work.Asymptotics.resCorr r τ)
    (hat : Work.LayerCont.layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
      = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) :
    windowChart ℓ d p t₀ A₁ ξ₁ A₂ ξ₂ r τ
      = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
        + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ := by
  rw [windowChart_eq, hlow]
  have h : Work.LayerCont.layerLowAt ℓ d p r τ + Work.Asymptotics.sinSqC r
        * Work.Asymptotics.resCorr r τ
        + Work.LayerCont.layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
        + Work.LayerCont.highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ
      = Work.LayerCont.layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
        + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ := by
    rw [Work.LayerCont.layerAt]; ring
  rw [h, hat]

end Work.LayerCont.FarTail
