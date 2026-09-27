import Mathlib
import Submission.Work.Drive.TripleMeetDefs

/-!
# The *seam* faces of a parametrised plane, and the cancellation they force

`Work.Drive.manifold_triple_inter_boundary_parity` counts the *boundary* triple intersections of three
`3`-chains, grouped by which of the three parameter cubes has reached its boundary.  In the chain route
each of the three chains is the sweep of a plane presented by a `2`-chain `y ↦ D k (y, s)`, where the
two coordinates `x 0`, `x 1` of the parameter are those of the plane's own presentation (a disk, or a
square with identifications) and `x 2` is the sweep parameter.  So the boundary of the `k`-th cube
splits into three geometrically different kinds of face:

* `x 2 = 1`: the plane `P_k` itself — these are the counts `n_P, n_Q, n_R`;
* `x 2 = 0`: the *bottom* end face of the sweep;
* `x 0 ∈ {0,1}` or `x 1 ∈ {0,1}`: the four **seam** faces, coming from the boundary of the plane's own
  2-chain presentation.

When the plane is presented by a *closed* surface — concretely, by a disk whose boundary circle is
identified antipodally with the cut (the situation of the disk model,
`Submission/Work/Drive/Surf/Model.lean`, and of the disk presentation of the capped plane
`Submission/Work/Drive/cappedPlaneCharts.lean`) — the seam faces are glued antipodally to one another,
so the antipodal involution `y ↦ (1 - y 0, 1 - y 1)` of the parameter square *fixes the plane's image*
on the seam and pairs the seam contributions up.  This file fixes the vocabulary: the seam boundary
triple intersections, and the involution that pairs them.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- **The antipodal involution of the parameter square, on the three cube coordinates.**  The first two
coordinates are replaced by their complements, the sweep coordinate is untouched.  On the boundary of
the square this is the antipodal map of the boundary circle, hence fixed-point free. -/
def seamInv (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun i : Fin 3 => if i = (2 : Fin 3) then x 2 else 1 - x i

@[simp] lemma seamInv_apply_zero (x : EuclideanSpace ℝ (Fin 3)) : seamInv x 0 = 1 - x 0 := rfl

@[simp] lemma seamInv_apply_one (x : EuclideanSpace ℝ (Fin 3)) : seamInv x 1 = 1 - x 1 := rfl

@[simp] lemma seamInv_apply_two (x : EuclideanSpace ℝ (Fin 3)) : seamInv x 2 = x 2 := by
  simp [seamInv]

/-- A point of the square is on its boundary. -/
def onSeam (x : EuclideanSpace ℝ (Fin 3)) : Prop :=
  x 0 = 0 ∨ x 0 = 1 ∨ x 1 = 0 ∨ x 1 = 1

/-- **The seam boundary triple intersections.**  The triples of `Work.Drive.tripleBdryMeet M D k` whose
`k`-th parameter lies on one of the four **seam** faces `x 0 ∈ {0,1}`, `x 1 ∈ {0,1}` of the cube (rather
than on the top face `x 2 = 1` of the plane or the bottom face `x 2 = 0` of the sweep). -/
def seamBdryMeet (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) :
    Set (Fin 3 → EuclideanSpace ℝ (Fin 3)) :=
  {x | x ∈ tripleBdryMeet M D k ∧ onSeam (x k)}

/-- **The top boundary triple intersections.**  The triples of `Work.Drive.tripleBdryMeet M D k`
whose `k`-th parameter lies on the **top** face `x 2 = 1` of its cube: geometrically, the `k`-th chain
has reached the plane presented by its own top face, and the count is the summand `n_P` (respectively
`n_Q`, `n_R`) of Hugelmeyer's parity identities. -/
def topBdryMeet (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) :
    Set (Fin 3 → EuclideanSpace ℝ (Fin 3)) :=
  {x | x ∈ tripleBdryMeet M D k ∧ x k 2 = 1}

/-- **The bottom boundary triple intersections.**  The triples of `Work.Drive.tripleBdryMeet M D k`
whose `k`-th parameter lies on the **bottom** face `x 2 = 0` of its cube: the end face of the sweep,
whose triple count is the end contribution `n_{-λ}` of Hugelmeyer's parity identities. -/
def bottomBdryMeet (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) :
    Set (Fin 3 → EuclideanSpace ℝ (Fin 3)) :=
  {x | x ∈ tripleBdryMeet M D k ∧ x k 2 = 0}

/-- The `k`-th block of a triple of parameters, with the seam involution applied to it. -/
def seamTriple (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  Function.update x k (seamInv (x k))

@[simp] lemma seamTriple_apply_self (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    seamTriple k x k = seamInv (x k) := by
  simp [seamTriple]

lemma seamTriple_apply_of_ne {k k' : Fin 3} (h : k' ≠ k)
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) : seamTriple k x k' = x k' := by
  simp [seamTriple, Function.update_of_ne h]

end Work.Drive
