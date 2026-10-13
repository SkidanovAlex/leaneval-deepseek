/-
# `Work.FTS.EllSol.EllPkgAux.TraceStmt` — the trace-class single-function interpolation

The single missing analytic input of the whole `FTS` elliptic machinery: the paper's §7
mixed-derivative interpolation

  `α² ∫_z mixIntS G ≤ C (α⁴ ∫_z ddIntS G + ∫_z ttIntS G + α² ∫_z dIntS G)`

for a datum `G` which is `C^∞` on the **open** quadrant, vanishes on the two angular boundary
lines (as values *and* as limits), whose slices of `G` and of `D_zG` have vanishing one-sided
traces at both endpoints, and which satisfies `SliceHonestOpen` together with the four outer
integrability hypotheses.

This module only records the statement (as a `def` of a `Prop`), so that several constructions
can refer to it; the existence of a constant is the crux (`interpOpenTrace`), proved elsewhere.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.EllipticEst.Core.i0Aux.InterpDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-- **The trace-class version of the open-quadrant single-function interpolation estimate.**  The
hypotheses are those of `Work.EllipticEst.Core.i0Aux.InterpOpen` together with the vanishing of
the angular *limits* of `G` and of `D_zG` at both endpoints (only the values `G z 0 = G z (π/2)`
are required by `InterpOpen`, which admits slices whose interior limits do not vanish). -/
def InterpOpenTraceStmt (C : ℝ) : Prop :=
  ∀ (α : ℝ) (G : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.SmoothOpen G →
    (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    Work.EllipticEst.Core.i0Aux.SliceHonestOpen G →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixIntS G z)
      Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ddIntS G z)
      Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ttIntS G z)
      Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.dIntS G z)
      Work.Spaces.Iz →
    α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
      ≤ C * (α ^ 4 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
          + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
          + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z))

end Work.FTS.EllSol.EllPkgAux
