import Submission.Work.Smooth.Jordan.Separation
import Submission.Work.Smooth.Jordan.wind_mem_int

/-!
# The index form of Jordan separation, and the full classical input of the plane

This file relates the two descriptions of the sides of a simple closed curve in the plane: the
**topological** one (`PlaneSeparation`: the complement is the disjoint union of an unbounded and a
bounded open preconnected set) and the **index** one (the sides are `{ind = 0}` and `{ind ≠ 0}`, and
`|ind| = 1` on the latter).

* `ind_eq_wind` — the index is the winding integral;
* `PlaneJordanSchoenflies c` — the _full_ classical input for a `C¹` simple closed curve in the
  plane: a separation, the value of the index on its two sides (this is the classical statement that
  a simple closed curve winds once around the points inside it and not at all around the points
  outside), and a spanning embedded disc whose image is the closure of the bounded side;
* `PlaneJordanSchoenflies.toPlaneSchoenflies` — its Schoenflies part.

Everything else of item 1 of the chapter (local constancy of the index, its vanishing at infinity,
the identification of the two components of the complement with the two index level sets, and
`|ind| ≤ 1`) is *derived* in the sibling modules:

| statement | module |
|---|---|
| `ind_local` | `Work.Smooth.Jordan.ind_local` |
| `ind_vanishes_at_infinity` | `Work.Smooth.Jordan.ind_vanishes_at_infinity` |
| `ind_const_on_preconnected` | `Work.Smooth.Jordan.ind_const_on_preconnected` |
| `ind_abs_le_one` | `Work.Smooth.Jordan.ind_abs_le_one` |
| `ind_eq_zero_iff`, `ind_ne_zero_iff` | `Work.Smooth.Jordan.ind_eq_zero_iff` |
| the standard circle satisfies the whole input | `Work.Smooth.Jordan.unitCircle_jordanSchoenflies` |
-/

open Set
open Classical

namespace Work.Smooth.Jordan

noncomputable section

/-- The index of a smooth closed curve is the winding integral. -/
theorem ind_eq_wind (c : SmoothPlaneCurve) {x : ℂ} (hx : x ∉ c.trace) :
    (ind c x : ℂ) = wind c x :=
  ind_spec c (wind_mem_int c hx)

/-- **The full classical input of the plane theory** for a `C¹` simple closed curve `c`: Jordan
separation with its two sides, the classical value of the index on them (zero on the unbounded side,
`±1` on the bounded side), and an embedded disc whose boundary is the curve and whose image is the
closure of the bounded side (Jordan–Schoenflies).

The first two clauses are the classical Jordan curve theorem together with the classical computation
of the winding number of a *simple* closed curve: it winds once around the points inside it and zero
times around the points outside.  Everything the chapter needs from the classical theory of simple
closed curves in the plane is contained in this structure. -/
structure PlaneJordanSchoenflies (c : SmoothPlaneCurve) where
  /-- Jordan separation of the curve -/
  sep : PlaneSeparation c.toPlaneCurve
  /-- the index vanishes on the unbounded side -/
  ind_eq_zero_U : ∀ x : ℂ, x ∈ sep.U → ind c x = 0
  /-- the index has modulus `1` on the bounded side -/
  ind_abs_eq_one_V : ∀ x : ℂ, x ∈ sep.V → |ind c x| = 1
  /-- the spanning embedding of the closed disc -/
  e : C(Disc, ℂ)
  /-- it is injective -/
  inj : Function.Injective e
  /-- its boundary is the curve -/
  boundary : ∀ θ : ℝ, e (circlePoint θ) = c.γ θ
  /-- its image is the closure of the bounded side -/
  range_e : Set.range e = closure sep.V

namespace PlaneJordanSchoenflies

variable {c : SmoothPlaneCurve}

/-- The Schoenflies part of the classical input. -/
def toPlaneSchoenflies (h : PlaneJordanSchoenflies c) : PlaneSchoenflies c.toPlaneCurve where
  simple := h.sep.simple
  U := h.sep.U
  V := h.sep.V
  isOpen_U := h.sep.isOpen_U
  isOpen_V := h.sep.isOpen_V
  preconn_U := h.sep.preconn_U
  preconn_V := h.sep.preconn_V
  nonempty_U := h.sep.nonempty_U
  nonempty_V := h.sep.nonempty_V
  disjoint_UV := h.sep.disjoint_UV
  union_eq := h.sep.union_eq
  bounded_V := h.sep.bounded_V
  e := h.e
  inj := h.inj
  boundary := h.boundary
  range_e := h.range_e

/-- The index of a point of the bounded side is `1` or `-1`. -/
theorem ind_eq_one_or_neg_one (h : PlaneJordanSchoenflies c) {x : ℂ} (hx : x ∈ h.sep.V) :
    ind c x = 1 ∨ ind c x = -1 := by
  have h1 : |ind c x| = 1 := h.ind_abs_eq_one_V x hx
  rcases abs_cases (ind c x) with ⟨h2, _⟩ | ⟨h2, _⟩
  · left
    rw [h2] at h1
    exact h1
  · right
    rw [h2] at h1
    linarith

/-- The index is nonzero on the bounded side. -/
theorem ind_ne_zero_V (h : PlaneJordanSchoenflies c) {x : ℂ} (hx : x ∈ h.sep.V) :
    ind c x ≠ 0 := by
  have h1 : |ind c x| = 1 := h.ind_abs_eq_one_V x hx
  intro h0
  rw [h0] at h1
  norm_num at h1

end PlaneJordanSchoenflies

end

end Work.Smooth.Jordan
