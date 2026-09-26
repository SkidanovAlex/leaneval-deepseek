import Mathlib
import Submission.Work.EpsW.Defs
import Submission.Work.InnermostDisk.Slicing
import Submission.Work.CountedPinch.Defs
import Submission.Work.BoxShrink.Core.Defs
import Submission.Work.Smooth.Plane.Slicing

/-!
# `ArcsWallFamily`: the wall of the half-box, in the arcs case, as a family of closed curves

This is the statement isolated in `Submission/Work/EpsW/NOTES_arcsCaseEps.md` §36--§37 as the *single*
missing local input of every wall/collar route to Pardon's Lemma 3 at the configurations where the
trace of the cutting plane leaves the box (the "arcs case").  It is the arcs-case counterpart of
`Work.Drive.EpsForm.halfBoxWall_trace_glued2`, which handles the *circles* case (its hypothesis
`Work.Smooth.Plane.TransversePlane P (cutDisc s c σ u)` forces the slice to be compact, hence a union
of circles, so its `hglue` input degenerates to the empty arc family).

**The two local hypotheses are not redundant (this is the correction of §36).**  Write
`Γ = P.carrier ∩ sphereSet c σ s` for the sphere trace and `Σ` for the slice.  At a point
`q ∈ P.carrier ∩ sphereSet c σ s ∩ cutPlane` (an "equator point", an endpoint of exactly one slice
arc, since the arcs are pairwise disjoint and injective), the wall `W = (Γ ∩ {level ≥ u}) ∪ closure Σ`
has, near `q`:

* one branch of `Γ` (with `level ≥ u`) if the level function crosses the value `u` on `Γ` at `q`:
  total `1 + 1 = 2` branches, and `W` is locally an arc;
* **no** branch of `Γ` if `q` is a strict local maximum of the level on `Γ`: total `1`, so `q` is a
  free endpoint of `W` and `W` is *not* a finite union of closed curves;
* **two** branches of `Γ` if `q` is a strict local minimum of the level on `Γ`: total `3`, a triod,
  and again no family of pairwise disjoint closed curves covers `W`.

The clauses are not redundant, and dropping any of them makes the statement **false** (the corrections
are recorded in `NOTES_arcsCaseEps.md` §§37 and 40):

* `hcross` rules out the strict local maximum (free endpoint) and the strict local minimum (triod) of
  the level on the trace at an equator point;
* `hend` (every equator point is an endpoint of a slice arc) encodes the transversality of the cutting
  plane at the equator points;
* `hint` (the arcs meet the box sphere only at their endpoints) rules out an *interior* tangency of the
  cutting plane, whose slice closure then has an isolated point;
* and the **endpoint clause** (both endpoints of every arc lie on the box sphere) rules out the
  remaining case, found by a colleague: a plane tangent to the surface *along an arc* of the slice whose
  two ends are free points strictly inside the box — there the wall's trace is locally a half-arc, and
  `hcross`, `hint` and `hend` all remain satisfied (they constrain the sphere trace and the equator
  points, neither of which sees the free ends of a slice arc in the interior of the box).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.EpsW

noncomputable section

/-- **The wall of the upper half-box**, as it appears inside this file: the closed upper cap of the box
sphere glued to the flat cutting disc.  It is definitionally the fleet's
`Work.Drive.EpsForm.halfBoxWall s c σ u` (`Submission/Work/Drive/EpsForm/epsBodyResidual.lean`), which
is repeated here so that this module does not have to import the (still `sorry`-carrying) module that
holds it. -/
abbrev wall (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  {y : R3 | Submission.boxNorm c σ y = s ∧ c (σ 2) + u ≤ y (σ 2)} ∪
    Work.BoxShrink.Core.cutDisc s c σ u

/-- The trace of the wall on the surface, pointwise. -/
theorem mem_wall_trace {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {x : R3} :
    x ∈ P.carrier ∩ wall s c σ u ↔
      x ∈ P.carrier ∧
        ((Submission.boxNorm c σ x = s ∧ c (σ 2) + u ≤ x (σ 2)) ∨
          x ∈ Work.BoxShrink.Core.cutDisc s c σ u) :=
  Iff.rfl

/-- **`ArcsWallFamily`.**  At a configuration whose box sphere is sliced by the surface (`Sl`), whose
sphere trace crosses the cutting plane at every point where it meets it (`hcross`), and whose slice
closure is *covered* by finitely many pairwise disjoint embedded arcs (`SliceArcsBody`, here unfolded:
the arcs are injective, their ranges are pairwise disjoint, they lie in the closure of the slice, and
they **cover** it) every *equator point* of which is an arc endpoint (`hend`), the trace of the half-box wall on the
surface is the union of the ranges of finitely many pairwise disjoint *simple* closed curves of the
surface.

The family is the one the fleet's consumer `Work.Drive.EpsForm.halfBoxWall_sphereSlicing` needs (it
turns such a family into `Work.InnermostDisk.SphereSlicing P (wall s c σ u)`, whence the counting makes
the trace inessential through `Work.EpsW.trace_inessential_of_slicing_of_subset_footprintWd`). -/
def ArcsWallFamily : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ∀ (Sl : Work.InnermostDisk.SphereSlicing P (Work.BoxShrink.Core.sphereSet c σ s)),
    (∀ (i : Sl.ι) (t : ℝ), (Sl.c i).γ t (σ 2) = c (σ 2) + u →
      (∀ ε : ℝ, 0 < ε → ∃ t' : ℝ, |t' - t| < ε ∧ c (σ 2) + u < (Sl.c i).γ t' (σ 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ t' : ℝ, |t' - t| < ε ∧ (Sl.c i).γ t' (σ 2) < c (σ 2) + u)) →
    ∀ (n : ℕ) (a : Fin n → C(Work.Smooth.Plane.ArcInterval, R3)),
      (∀ j : Fin n, Function.Injective (a j)) →
      (∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
        a j x ∈ closure (Work.BoxShrink.Core.sliceRegion P s c σ u)) →
      (Pairwise fun j j' : Fin n => Disjoint (Set.range (a j)) (Set.range (a j'))) →
      (closure (Work.BoxShrink.Core.sliceRegion P s c σ u) ⊆ ⋃ j, Set.range (a j)) →
      -- the arcs meet the box sphere only at their endpoints: their interiors lie in the open box
      (∀ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
        a j x ∈ Work.BoxShrink.Core.sphereSet c σ s → ((x : ℝ) = 0 ∨ (x : ℝ) = 1)) →
      -- ... and their endpoints *do* lie on the box sphere (no arc ends in the interior)
      (∀ j : Fin n,
        a j ⟨0, by norm_num⟩ ∈ Work.BoxShrink.Core.sphereSet c σ s ∧
          a j ⟨1, by norm_num⟩ ∈ Work.BoxShrink.Core.sphereSet c σ s) →
      (∀ q ∈ P.carrier ∩ Work.BoxShrink.Core.sphereSet c σ s ∩ Work.BoxShrink.Core.cutPlane c σ u,
        ∃ (j : Fin n) (x : Work.Smooth.Plane.ArcInterval),
          ((x : ℝ) = 0 ∨ (x : ℝ) = 1) ∧ a j x = q) →
      ∃ (m : ℕ) (γ : Fin m → Work.CoreTopology.ClosedCurve P),
        (∀ i : Fin m, Work.CoreTopology.IsSimple P (γ i)) ∧
        (∀ i j : Fin m, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) ∧
        (⋃ i, Set.range (γ i).γ) = P.carrier ∩ wall s c σ u

end

end Work.EpsW
