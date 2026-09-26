import Submission.Work.BoxShrink.PinchOff.CompactSlice
import Submission.Work.BoxShrink.PinchOff.ArcsOnly

/-!
# The honest tameness predicate: arcs whose ends run to the box sphere

`Work.BoxShrink.Pinch.TameSlice` (and `SliceArcsOnly`) parametrise the pieces of the trace over the
**compact** interval `Work.Smooth.Plane.ArcInterval` and *require their ranges to lie in the slice*
`Σ = Sigma ψ s c σ u = F ∩ {boxNorm < s} ∩ {G = 0}`.  Since the box is defined with a strict
inequality, a genuine arc of the trace — one whose endpoint lies on the box sphere `{boxNorm = s}` —
is open at that end and is contained in no compact subset of `Σ`; hence those predicates force `Σ` to
be compact (`isCompact_sigma_of_tameSlice`, `ResidualHolds.lean`), which excludes exactly the
configuration family Pardon's Lemma 3 is about (the plane's trace leaving the box: e.g. the standard
torus with `σ = swap 1 2`, `s = 5/2`, `c = u = 0`, whose slice is two open arcs).

This module supplies the honest predicate, `TameClosedSlice`: the pieces of the trace are
parametrised over the compact interval but are required to lie in the **closure** of the slice, and to
cover it.  That is the statement that the *closed* slice — the trace of the cutting plane cut by the
closed box, i.e. the arcs with their ends included — is a finite union of arcs and circles of the
surface; the ends of its arcs lie on the box sphere (`closure (Sigma …) \ Sigma … ⊆ {boxNorm = s}`),
which is precisely the structural fact the pinch argument uses.  At such a configuration `Σ` itself
need **not** be compact, and the residue of the residual is the genuinely geometric case.

The split of `CompactSlice.lean`/`PerpCases.lean` carries over verbatim:

* `TraceClosedSliceResidual` — the residual for configurations with a transverse, closed-tame slice,
  whose slice carries no essential loop;
* `TraceClosedNonCompactSlice` — the *honest* form of the remaining case: the slice is not compact,
  i.e. the trace of the cutting plane really leaves the box;
* `traceClosedSliceResidual_of_nonCompact` — the residual follows from that case, because a compact
  slice under the box-local transversality is a finite union of circles and the circles-only theorem
  applies (`tracePerpRealisable_of_isCompact_slice`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- **The honest tameness predicate.**  The pieces of the trace of the cutting plane are parametrised
over the compact interval — so they are arcs of the surface with their ends included — and they cover
the *closure* of the slice.  Unlike `SliceArcsOnly` / `TameSlice` this does **not** force the slice to
be compact: the ends of the arcs may lie on the box sphere `{boxNorm = s}`, which the (open) box
excludes, so the slice itself is the union of the interiors of the arcs. -/
def TameClosedSlice (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (a : κ → C(Work.Smooth.Plane.ArcInterval, R3))
    (n : ℕ) (γ : Fin n → Work.CoreTopology.ClosedCurve (surface ψ)),
    (∀ (j : κ) (t : Work.Smooth.Plane.ArcInterval), a j t ∈ closure (Sigma ψ s c σ u)) ∧
    (∀ (i : Fin n) (t : ℝ), γ i t ∈ closure (Sigma ψ s c σ u)) ∧
    (∀ x : R3, x ∈ closure (Sigma ψ s c σ u) →
      (∃ j : κ, x ∈ Set.range (a j)) ∨ (∃ i : Fin n, x ∈ Set.range (γ i).γ))

/-- **The residual for configurations with a closed-tame slice** (the honest replacement for
`TracePerpSlice` at the configurations Pardon's lemma is about). -/
def TraceClosedSliceResidual : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u

/-- **The genuinely geometric case of the residual**: the slice is a union of arcs whose ends run to
the box sphere, so it is not compact (the trace of the cutting plane leaves the box).  This is the
statement a faithful formalisation of Pardon's Lemma 3 has to prove. -/
def TraceClosedNonCompactSlice : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
    ¬ IsCompact (Sigma ψ s c σ u) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u

/-- **The residual follows from its non-compact case**: at a compact slice the box-local
transversality makes the slice a finite union of circles, and the circles-only theorem applies. -/
theorem traceClosedSliceResidual_of_nonCompact (h : TraceClosedNonCompactSlice) :
    TraceClosedSliceResidual := by
  intro ψ s c σ u hT _hTa hZ
  by_cases hc : IsCompact (Sigma ψ s c σ u)
  · exact tracePerpRealisable_of_isCompact_slice hT hc hZ
  · exact h ψ s c σ u hT ‹_› hc hZ

end

end Work.BoxShrink.PinchOff
