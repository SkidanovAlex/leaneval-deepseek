import Mathlib
import Submission.Work.Stems.HurewiczSphere
import Submission.Work.RatHurewicz.Excision

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two thickened hemispheres of `S^{n+1}` and the "connector" structure

This file fixes the vocabulary for the proof of
`Work.RatHurewicz.freudenthalTorsionTransfer` (Freudenthal's suspension result), which is carried
out by writing `S^{n+1}` as the union of the two *thickened hemispheres*

* `upperHem n = {x : S^{n+1} | -1/2 < x_{n+1}}`,
* `lowerHem n = {x : S^{n+1} | x_{n+1} < 1/2}`,

with intersection the *thickened equator* `{x | |x_{n+1}| < 1/2} ∋ equator n = {x | x_{n+1} = 0}`.

Everything is phrased for the model `Work.Stems.sphere n = Metric.sphere 0 1 ⊆ ℝ^{n+1}` of the
`n`-sphere, which is the model of `Work.Stems.FreudenthalTorsionTransfer`.

## The connector structure

`Connector Y` is the existence of a *continuous choice of paths between any two points of `Y`,
degenerating on the diagonal*: a continuous `c : Y × Y × I → Y` with `c (p, q, 0) = p`,
`c (p, q, 1) = q` and `c (p, p, t) = p`.

For a subset of a sphere that is the complement of a closed spherical cap, such a connector exists:
such a set is the image of a Euclidean *ball* (convex!) under stereographic projection, and one uses
the straight lines of the ball.  The connector is what replaces the convexity of a ball in the
proof that the relative homotopy groups `π_k(Y, A)` of a pair vanish in the range where `A` is
connected — see `Work.RatHurewicz.relPiVanishingOfConnector`.
-/

open scoped Topology
open Metric

namespace Work.RatHurewicz

noncomputable section

/-- The `n`-sphere `Sⁿ ⊆ ℝ^{n+1}`, in the model `Work.Stems.sphere n` (the model of the statement
`Work.Stems.FreudenthalTorsionTransfer`). -/
abbrev Sph (n : ℕ) : Type := Work.Stems.sphere n

/-- The last coordinate functional on `ℝ^{m+1}`. -/
def lastC (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 1))) : ℝ := x.ofLp (Fin.last m)

theorem continuous_lastC (m : ℕ) : Continuous (lastC m) :=
  PiLp.continuous_apply 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m)

/-- The **upper thickened hemisphere** `{x ∈ S^{n+1} : x_{n+1} > -1/2}`. -/
def upperHem (n : ℕ) : Set (Sph (n + 1)) := {x | -(1 / 2 : ℝ) < lastC (n + 1) x}

/-- The **lower thickened hemisphere** `{x ∈ S^{n+1} : x_{n+1} < 1/2}`. -/
def lowerHem (n : ℕ) : Set (Sph (n + 1)) := {x | lastC (n + 1) x < 1 / 2}

/-- The **equator** `{x ∈ S^{n+1} : x_{n+1} = 0}`. -/
def equator (n : ℕ) : Set (Sph (n + 1)) := {x | lastC (n + 1) x = 0}

/-- A **connector** of a topological space: a continuous choice of paths between any two points,
degenerating on the diagonal. -/
structure Connector (Y : Type*) [TopologicalSpace Y] where
  /-- the connecting path -/
  c : C(Y × Y × unitInterval, Y)
  /-- the path starts at the first point -/
  zero : ∀ p q, c (p, q, 0) = p
  /-- the path ends at the second point -/
  one : ∀ p q, c (p, q, 1) = q
  /-- the path is constant when the two points coincide -/
  diag : ∀ p t, c (p, p, t) = p

end

end Work.RatHurewicz
