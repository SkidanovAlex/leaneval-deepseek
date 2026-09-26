import Submission.Work.Smooth.Jordan.Index

/-!
# Separation of the plane by a simple closed curve, and Schoenflies in the plane

This file sets up the two structures in which the classical separation theory of a simple closed
curve in the plane is consumed.

* `PlaneSeparation c` — Jordan separation: the complement of the trace of `c` is the disjoint
  union of two non-empty preconnected open sets `U` (the outside) and `V` (the bounded inside);
* `PlaneSchoenflies c` — Jordan–Schoenflies: in addition the closure of the bounded inside is the
  image of the closed disc under an embedding whose boundary is `c`.

Everything elementary is *derived* from these structures in the sibling modules of this directory:
the two sides are exactly the level sets `{ind = 0}` and `{ind ≠ 0}` of the index, the index takes
the values `0` and `±1`, the inside is the image of the open disc under the spanning embedding, and
a curve contained in a closed convex set bounds a disc contained in that set.

The classical input itself is isolated as `Work.Smooth.Jordan.JordanInput` and
`Work.Smooth.Jordan.SchoenfliesInput` at the end of this file; `ClassicalInput` collects both.
-/

open Set
open Classical

namespace Work.Smooth.Jordan

noncomputable section

/-- **Jordan separation for a simple closed curve in the plane.**  The complement of the trace is
the disjoint union of two non-empty preconnected open sets: the *outside* `U` and the *inside* `V`,
the latter being bounded. -/
structure PlaneSeparation (c : PlaneCurve) where
  /-- the curve is simple -/
  simple : PlaneCurve.IsSimple c
  /-- the unbounded side -/
  U : Set ℂ
  /-- the bounded side -/
  V : Set ℂ
  /-- the unbounded side is open -/
  isOpen_U : IsOpen U
  /-- the bounded side is open -/
  isOpen_V : IsOpen V
  /-- the unbounded side is preconnected -/
  preconn_U : IsPreconnected U
  /-- the bounded side is preconnected -/
  preconn_V : IsPreconnected V
  /-- the unbounded side is non-empty -/
  nonempty_U : U.Nonempty
  /-- the bounded side is non-empty -/
  nonempty_V : V.Nonempty
  /-- the two sides are disjoint -/
  disjoint_UV : Disjoint U V
  /-- together they exhaust the complement of the curve -/
  union_eq : U ∪ V = c.traceᶜ
  /-- the bounded side is bounded -/
  bounded_V : Bornology.IsBounded V

namespace PlaneSeparation

variable {c : PlaneCurve}

theorem isConnected_U (h : PlaneSeparation c) : IsConnected h.U :=
  ⟨h.nonempty_U, h.preconn_U⟩

theorem isConnected_V (h : PlaneSeparation c) : IsConnected h.V :=
  ⟨h.nonempty_V, h.preconn_V⟩

theorem mem_iff (h : PlaneSeparation c) {x : ℂ} (hx : x ∉ c.trace) :
    x ∈ h.U ↔ x ∉ h.V := by
  constructor
  · intro hxU hxV
    exact Set.disjoint_left.mp h.disjoint_UV hxU hxV
  · intro hxV
    have : x ∈ h.U ∪ h.V := by rw [h.union_eq]; exact hx
    rcases this with h' | h'
    · exact h'
    · exact absurd h' hxV

end PlaneSeparation

/-- **Jordan–Schoenflies for a simple closed curve in the plane**: Jordan separation together with
an embedded closed disc whose boundary is the curve and whose image is the closure of the bounded
side.  This is the classical Schoenflies theorem in the plane, in the form consumed by the
innermost-disc cut-and-paste. -/
structure PlaneSchoenflies (c : PlaneCurve) extends PlaneSeparation c where
  /-- the spanning embedding of the closed disc -/
  e : C(Disc, ℂ)
  /-- it is injective -/
  inj : Function.Injective e
  /-- its boundary is the curve -/
  boundary : ∀ θ : ℝ, e (circlePoint θ) = c.γ θ
  /-- its image is the closure of the bounded side -/
  range_e : Set.range e = closure V

namespace PlaneSchoenflies

variable {c : PlaneCurve}

/-- A Schoenflies datum exhibits the curve as the boundary of an embedded disc. -/
theorem boundsDisc (h : PlaneSchoenflies c) : BoundsDisc c :=
  ⟨h.e, h.inj, h.boundary⟩

end PlaneSchoenflies

/-! ## The classical input -/

/-- **Jordan separation as a property of a simple closed curve in the plane**: the classical
input. -/
def JordanInput (c : PlaneCurve) : Prop := PlaneCurve.IsSimple c → Nonempty (PlaneSeparation c)

/-- **Jordan–Schoenflies as a property of a simple closed curve in the plane**: the classical
input. -/
def SchoenfliesInput (c : PlaneCurve) : Prop := PlaneCurve.IsSimple c → Nonempty (PlaneSchoenflies c)

/-- The complete classical input of the plane theory. -/
def ClassicalInput : Prop := ∀ c : PlaneCurve, PlaneCurve.IsSimple c → Nonempty (PlaneSchoenflies c)

/-- `SchoenfliesInput` is the same thing as `ClassicalInput` restricted to `c`. -/
theorem schoenfliesInput_iff_classicalInput (c : PlaneCurve) :
    SchoenfliesInput c ↔ (PlaneCurve.IsSimple c → Nonempty (PlaneSchoenflies c)) := Iff.rfl

/-- Schoenflies implies Jordan separation. -/
theorem jordanInput_of_schoenfliesInput {c : PlaneCurve} (h : SchoenfliesInput c) :
    JordanInput c :=
  fun hs => (h hs).elim fun d => ⟨d.toPlaneSeparation⟩

/-- A `PlaneSchoenflies` datum is a `PlaneSeparation` datum. -/
theorem Nonempty.planeSeparation_of_schoenflies {c : PlaneCurve}
    (h : Nonempty (PlaneSchoenflies c)) : Nonempty (PlaneSeparation c) :=
  h.elim fun d => ⟨d.toPlaneSeparation⟩

end

end Work.Smooth.Jordan
