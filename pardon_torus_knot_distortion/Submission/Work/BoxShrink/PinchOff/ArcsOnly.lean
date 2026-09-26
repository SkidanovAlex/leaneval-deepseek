import Submission.Work.BoxShrink.PinchOff.CirclesCase

/-!
# The residual restricted to the arcs of the trace

`CirclesCase.lean` proves that the *closed* components of any tame slicing datum peel away
(`exists_closedComponents_peeling`), so the remaining content of the corrected residual
(`TracePerpSlice`, `Perp.lean`) is exactly the **arcs** of the trace.  This module isolates that
content as a named statement (`TraceArcsResidual`), together with the structural hypothesis of the
case (`SliceArcsOnly`, the exact analogue of `SliceCirclesOnly`), so that the remaining mathematics is
a single, sharply stated obligation.

## What is known about it (`README.md` §18.2)

Working in the parameter plane (`Ω̃ = {B < s}`, the trace `Z̃ = Ω̃ ∩ {G = 0}`, `Ũ = Ω̃ \\ Z̃`), the
statement is: a lattice period `v ≠ 0` realised in `Ω̃` is realised in `Ũ`.  The components of `Z̃` are
compact (arcs with endpoints on `∂Ω̃`, and circles), so no single curve blocks a period; the
obstruction is a **closed wall** made of trace arcs together with pieces of the sphere trace.  Two
facts are available:

* the two-crossings (detour) move works whenever the two crossings lie on the *same* trace arc: the
  plane is simply connected, so replacing the piece of the path between them by the sub-arc of the
  trace is a homotopy rel endpoints (hence preserves the winding vector), and the closed sub-arc
  between two crossings is a compact subset of the open `Ω̃`, so the move stays inside `Ω̃`;
* the trace line `L` of (K0) is one-dimensional and the class of every wall lies in it, so the
  hypothesis `cross ([γ], v) = 0` of the parent's factored residual kills `cross([γ], [W])` for
  *every* wall `W`: the number of crossings of `γ` with the trace arcs **of a single wall** is even.

What is missing is the **geometric pairing** of those crossings: an odd count on one arc of a wall
must be compensated on another arc of the same wall, and a pairing *along the wall* passes through the
outside `Ō`, which a path inside the open `Ω̃` cannot do.  It is here that the convexity of Pardon's box
(`exists_path_avoiding_of_convex`, `Convex.lean`) has to enter.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- **The slice of the configuration consists of arcs only.**  There is a finite family of embedded
arcs of the surface, carried by the slice, covering the slice.  This is the "no circles" case of
`Work.Smooth.Plane.TransversePlane`, restricted to the slice region inside the box; it is the exact
analogue of `SliceCirclesOnly`. -/
def SliceArcsOnly (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (a : κ → C(Work.Smooth.Plane.ArcInterval, R3)),
    (∀ j, Function.Injective (a j)) ∧
    (∀ (j : κ) (t : Work.Smooth.Plane.ArcInterval), a j t ∈ Sigma ψ s c σ u) ∧
    (∀ x : R3, x ∈ Sigma ψ s c σ u → ∃ j : κ, x ∈ Set.range (a j))

/-- **The residual restricted to the arcs of the trace** — the one remaining obligation of the pinch.
For every smooth configuration with a transverse slice whose trace consists of arcs only and which
carries no essential loop, the parent's factored statement `TracePerpRealisable` holds. -/
def TraceArcsResidual : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
    SliceArcsOnly ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u

/-- **`TraceArcsResidual` gives the corrected residual** at the configurations whose slice consists of
arcs only: this is `TracePerpSlice` with the structural hypothesis of the case, which is what the
circles-only theorem `CirclesCase.lean` does for the circles. -/
theorem tracePerpSlice_of_traceArcsResidual (h : TraceArcsResidual) :
    ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      SliceArcsOnly ψ s c σ u →
      ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
      Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u :=
  h

end

end Work.BoxShrink.PinchOff
