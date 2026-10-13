/-
# `Work.FTS.EllSol.EllPkgAux.MollBase` — the vocabulary of the mollification transfer

This module fixes the *hypothesis package* under which the trace-class interpolation estimate
`Work.FTS.EllSol.EllPkgAux.InterpOpenTraceStmt` is proved, together with the definitions shared
by the pieces of the proof: the θ-mollified datum `thMoll` and the log-radial mollification
`zmoll` of `Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs`, and the *strip-admissibility*
predicate that says that the doubly-mollified datum satisfies the hypotheses of the (proved)
strip-class estimate `Work.EllipticEst.Core.i0Aux.InterpStrip`.

Nothing here is a statement of the target: the three analytic pieces
(`Work.FTS.EllSol.EllPkgAux.mollStripAdm`, `...mollDom`, `...mollFatou`) live in their own
modules, and the assembly in `interpOpenTrace`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.EllipticEst.Core.i0Aux.InterpDefs
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.Core.i0Aux.interpS_theta
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

/-- **The hypothesis package of the trace-class single-function interpolation.**  This is
verbatim the tuple of hypotheses of `InterpOpenTraceStmt` (for the datum `G`): smoothness on
the open quadrant, the two endpoint *values*, the four vanishing endpoint *traces* of `G` and
of `D_zG`, and slicewise honesty of the three right-hand-side slots. -/
def TraceClass (G : ℝ → ℝ → ℝ) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen G ∧
  (∀ z : ℝ, G z 0 = 0) ∧ (∀ z : ℝ, G z (Real.pi / 2) = 0) ∧
  (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
  (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => G z θ)
    (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) ∧
  (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
  (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
    (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) ∧
  Work.EllipticEst.Core.i0Aux.SliceHonestOpen G

/-- The four outer `z`-integrability hypotheses of `InterpOpenTraceStmt`, bundled. -/
def FourInts (G : ℝ → ℝ → ℝ) : Prop :=
  MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixIntS G z) Work.Spaces.Iz ∧
  MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ddIntS G z) Work.Spaces.Iz ∧
  MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.ttIntS G z) Work.Spaces.Iz ∧
  MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.dIntS G z) Work.Spaces.Iz

/-- **Strip-admissibility of the doubly-mollified datum**: `zmoll G δ ε` is smooth on the
half strip `(0,∞) × (-1, π/2+1)` (hence `C^∞` across both angular boundary lines) and vanishes
on the two boundary lines.  These are exactly the smoothness hypotheses of
`Work.EllipticEst.Core.i0Aux.InterpStrip`. -/
def StripAdm (G : ℝ → ℝ → ℝ) (δ ε : ℝ) : Prop :=
  (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε))
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))) ∧
  (∀ z : ℝ, Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z 0 = 0) ∧
  (∀ z : ℝ, Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z (Real.pi / 2) = 0)

/-- The two-sided *validity window* of the mollification parameters. -/
def Params (δ ε : ℝ) : Prop := 0 < ε ∧ ε ≤ 1 / 2 ∧ 0 < δ ∧ δ ≤ 1 / 2

end Work.FTS.EllSol.EllPkgAux
