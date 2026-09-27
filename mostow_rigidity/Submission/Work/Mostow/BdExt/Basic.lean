import Mathlib
import Submission.Mostow.Interfaces

/-!
# Boundary extension of a quasi-isometry: basic definitions

This module sets up the explicit chart-level calculus used to build the boundary map of a
quasi-isometry of `ℍⁿ` (area C4, `BoundaryExtProp`).

Everything is expressed in the chart `E n` of `Submission.Mostow.Interfaces`:
* `hdist` is the hyperbolic distance,
* `Sph n` is the boundary sphere,
* `ray ξ t = sinh t • ξ` is the geodesic ray from the chart origin `0` to `ξ ∈ Sph n`,
  parametrised by hyperbolic arclength,
* `lvl u = hdist 0 u` is the "hyperbolic level" of `u` (its distance to the origin),
* `dirv u` is the Euclidean direction of `u` as seen from the origin (junk at `0`),
* `gpr a u v` is the Gromov product of `u` and `v` with base point `a`.

The key relation (the hyperbolic law of cosines for the triangle `0, u, v`) is that
`cosh (hdist u v) = cosh (lvl u) * cosh (lvl v) - sinh (lvl u) * sinh (lvl v) * ⟪dirv u, dirv v⟫`,
so that the "angle" between `dirv u` and `dirv v` is controlled by the level and the mutual
distance.  This is the engine of the whole boundary-extension argument.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The geodesic ray from the chart origin to `ξ`, parametrised by hyperbolic arclength:
`ray ξ t = sinh t • ξ`.  For `ξ ∈ Sph n` we have `hdist 0 (ray ξ t) = t`. -/
def ray (ξ : E n) (t : ℝ) : E n := Real.sinh t • ξ

/-- The hyperbolic "level" of a point: its distance to the chart origin. -/
def lvl (u : E n) : ℝ := hdist 0 u

/-- The Euclidean direction of `u` as seen from the origin (junk at `u = 0`):
`dirv u = ‖u‖⁻¹ • u`.  For `u ≠ 0` this is a unit vector. -/
def dirv (u : E n) : E n := (‖u‖)⁻¹ • u

/-- The Gromov product of `u` and `v` with base point `a`. -/
def gpr (a u v : E n) : ℝ := (hdist a u + hdist a v - hdist u v) / 2

/-- A sequence converges to the boundary point `ξ`: it escapes to infinity and its directions
converge to `ξ`.  This is convergence in the visual compactification of `ℍⁿ`. -/
def ConvTo (u : ℕ → E n) (ξ : E n) : Prop :=
  Filter.Tendsto (fun k => ‖u k‖) Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun k => dirv (u k)) Filter.atTop (nhds ξ)

/-- Two sequences are at bounded distance from one another. -/
def CloseSeq (u v : ℕ → E n) : Prop := ∃ D : ℝ, ∀ k, hdist (u k) (v k) ≤ D

end

end Work.Mostow.BdExt
