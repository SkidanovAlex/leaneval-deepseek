import Submission.Work.BoxShrink.Pinch.TraceClass
import Submission.Work.BoxShrink.Pinch.TraceSpanLeOneSmoothHolds

/-!
# (K0) is a theorem: the trace of a transverse plane carries no two independent classes

`TraceSpanLeOneSmoothHolds` (`TraceSpanLeOneSmoothHolds.lean`, proved by a delegated colleague)
discharges ingredient **(K0)** of Pardon's pinch for the smooth tori of the challenge: for a smooth
torus `F = ψ(F_standard)` and a plane transverse to `F` along the whole trace, the winding span of
the trace `F ∩ {y (σ 2) = c (σ 2) + u}` is at most one-dimensional.

The proof does not need the missing "a loop of a component of the trace is homotopic to a multiple of
that component": it pushes an arbitrary loop `γ` of the trace *off* the trace — `0` is a regular value
of the plane coordinate and the critical values are closed, so the normalised gradient flow homotopes
`γ` into `{g < a}` with `a < 0` without changing its winding class
(`Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region`,
`Work.SurgeryInvariance.WindingOf.homotopic_eq`); the pushed loop is disjoint from the trace, so
`Work.BoxShrink.Pinch.DisjointLoopsWindingDet` applies.

This module records the consequences of (K0) in the vocabulary of the chapter:

* `traceLineSmooth_holds` — the chapter's `TraceLineSmooth` is a theorem;
* `finrank_windingSpan_cutPlane_le_one` — the form without the `carrier ∩ …`;
* `windingSpan_planeTrace_le_one`, `exists_traceLine_of_transverseTrace`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **(K0) for the smooth tori of the challenge is a theorem** (the chapter's `TraceLineSmooth`). -/
theorem traceLineSmooth_holds : TraceLineSmooth :=
  traceLineSmooth_of_traceSpanLeOneSmooth TraceSpanLeOneSmoothHolds

/-- **(K0) in the dimension form**, for the cutting plane itself rather than the trace of the
surface. -/
theorem finrank_windingSpan_cutPlane_le_one (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (hT : TransverseTrace ψ c σ u) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.cutPlane c σ u)) ≤ 1 := by
  rw [← windingSpan_planeTrace]
  exact TraceSpanLeOneSmoothHolds ψ c σ u hT

/-- **(K0) in the dimension form**, in the vocabulary of the trace. -/
theorem windingSpan_planeTrace_le_one (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (hT : TransverseTrace ψ c σ u) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (planeTrace (Work.Smooth.Morse.torus ψ) c σ u)) ≤ 1 :=
  TraceSpanLeOneSmoothHolds ψ c σ u hT

/-- **The trace has a line** for every transverse plane. -/
theorem exists_traceLine_of_transverseTrace (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (hT : TransverseTrace ψ c σ u) :
    ∃ L : Submodule ℚ (ℚ × ℚ), TraceLine (Work.Smooth.Morse.torus ψ) c σ u L :=
  traceLineSmooth_holds ψ c σ u hT

end

end Work.BoxShrink.Pinch
