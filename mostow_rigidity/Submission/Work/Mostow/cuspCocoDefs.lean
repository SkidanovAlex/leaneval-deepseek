import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.geomFiniteDefs

/-!
# Area C1 (geomFinite) — vocabulary for `cuspCocompactAtLevel` (G7)

The cusp stabiliser of a lattice acts cocompactly on the horospheres at its fixed point.
The classical proof computes the volume of the cusp region `H/Γ_ξ` in *horospherical
coordinates*: if `ξ ∈ Sph n` is a boundary point, the horospheres `lev ξ · = D` are flat and
carry a level-independent flat coordinate `yc ξ ·`, so the horoball `{lev ξ · < D}` decomposes
as `(ξ^⊥) × (0,D)`; the group `Γ_ξ` preserves the level and acts on `ξ^⊥` by a *level
independent* group of Euclidean isometries, and the hyperbolic volume element is a positive
multiple of the flat one.  Hence the cusp has finite volume iff the flat quotient `ξ^⊥/Γ_ξ`
has finite covolume, i.e. iff `Γ_ξ` is cocompact on the horosphere.

This file collects the definitions used by that argument (see `QIDefs` for `lev`, `wc`, `yc`,
`hptOf`).

* `htrans ξ v` — the horospherical translation ("transvection") by `v ∈ ξ^⊥`; it preserves the
  level of the Busemann function and acts on the flat coordinate by `y ↦ y - v/2`.
* `hbox ξ A I` — the "horospherical box" over a set `A ⊆ ξ^⊥` of flat coordinates and an
  interval `I` of levels.
* `volY ξ` — the flat `(n-1)`-dimensional Lebesgue measure on `ξ^⊥`, viewed as a measure on `E n`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The horospherical translation (transvection) of `ℍⁿ` at the boundary point `ξ` by the
tangential vector `v ∈ ξ^⊥`: in the flat coordinate `yc ξ` it acts by `y ↦ y - v/2`, and it
preserves the levels of `lev ξ`. -/
def htrans (ξ v u : E n) : E n :=
  u - ((lev ξ u) / 2) • v + (((lev ξ u) * ‖v‖ ^ 2 / 8) - (inner ℝ u v) / 2) • ξ

/-- The horospherical box over a set `A` of flat coordinates at `ξ` and an interval `I` of
levels: the set of points of `ℍⁿ` whose flat coordinate lies in `A` and whose level lies in
`I`. -/
def hbox (ξ : E n) (A : Set (E n)) (I : Set ℝ) : Set (E n) :=
  {u | yc ξ u ∈ A ∧ lev ξ u ∈ I}

/-- The flat `(n-1)`-dimensional Lebesgue measure on `ξ^⊥ ⊆ E n`, transported to `E n`. -/
def volY (ξ : E n) : Measure (E n) :=
  Measure.map (Subtype.val : (Submodule.span ℝ ({ξ} : Set (E n)))ᗮ → E n)
    (Measure.addHaar : Measure (Submodule.span ℝ ({ξ} : Set (E n)))ᗮ)

/-- The set of points of the level `D` horosphere of `ξ` over a set `A` of flat coordinates. -/
def levOver (ξ : E n) (A : Set (E n)) (D : ℝ) : Set (E n) :=
  {u | yc ξ u ∈ A ∧ lev ξ u = D}

end

end Work.Mostow
