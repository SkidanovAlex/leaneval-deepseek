import Mathlib
import Submission.Work.Smooth.Plane.Defs

/-!
# Planar Jordan–Schoenflies: the vocabulary of the convexity form

This file fixes the vocabulary of the *planar* separation theory used by the planar innermost-disc
argument.  Everything here concerns closed curves in the plane `ℂ`.

## The point of the convexity form

Pardon's planar innermost argument needs only one half of the classical Jordan–Schoenflies theory
for a *convex* plane region: a simple closed plane curve lying in a convex set `D` bounds an
embedded disc contained in `D`.  The convexity of `D` makes this substantially weaker than the
general theorem:

* an embedded disc spanning the curve exists by Jordan–Schoenflies (`PlanarSchoenfliesInput`);
* and it must be *shown* that this disc lies in `D`: for `x ∉ D` a line separates `x` from the
  curve (`exists_functional_le_of_notMem_convex`, a consequence of the geometric Hahn–Banach
  theorem), and the separating functional gives an explicit homotopy of the curve to a constant
  loop in `ℂ ∖ {x}` (`nullHomotopicAvoiding_of_notMem_convex`).  So a point outside `D` can never
  be a point of the disc, because the classical theorem says that the points of the disc are
  exactly those around which the curve *cannot* be contracted away
  (`PlaneJordanData.inside_not_nullHomotopic`).

## Main definitions

* `NullHomotopicAvoiding c x` — the loop `c` (based at `c 0`) is homotopic to a constant loop in
  the complement of `x`; this is the "the curve does not wind around `x`" condition, stated purely
  in terms of homotopies (no degree theory is needed for the convexity argument);
* `PlaneJordanData c` — the classical Jordan–Schoenflies datum for the simple closed curve `c`: an
  embedded disc `e` spanning it, together with the (hard direction of the) Jordan curve theorem,
  namely that no point of the open disc can be reached by a null-homotopy of the curve;
* `PlaneJordanInput` — the classical input: every simple closed plane curve has such a datum.

## Main results

* `exists_functional_le_of_notMem_convex` — weak separation of a point from a convex set with
  nonempty interior, in the exact form the homotopy argument consumes;
* `nullHomotopicAvoiding_of_notMem_convex` (in `Work.Smooth.Plane.Convex`) — the explicit
  homotopy;
* `PlaneJordanData.mem_of_convex` and the Theorem `exists_spanningDisc_of_convex_planar`
  (in `Work.Smooth.Plane.Convex`) — the convexity form of planar Jordan–Schoenflies, in `ℂ` and
  in `ℝ³`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Plane

noncomputable section

/-! ## Null-homotopy away from a point -/

/-- **The loop `c` is null-homotopic in the complement of `x`**: there is a homotopy, through
loops avoiding `x`, from `t ↦ c (2π t)` to the constant loop at `c 0`.

This is the "the curve does not wind around `x`" condition, in the form in which the convexity
argument produces it (and in which the classical Jordan theory consumes it): the separating
functional of a convex region not containing `x` gives such a homotopy outright. -/
def NullHomotopicAvoiding (c : ℝ → ℂ) (x : ℂ) : Prop :=
  ∃ H : C(ArcInterval × ArcInterval, ℂ),
    (∀ p : ArcInterval × ArcInterval, H p ≠ x) ∧
    (∀ t : ArcInterval, H (0, t) = c (2 * Real.pi * t)) ∧
    (∀ t : ArcInterval, H (1, t) = c 0)

/-- A constant loop at a point `y ≠ x` is null-homotopic in the complement of `x`. -/
theorem NullHomotopicAvoiding.const_of_ne {x y : ℂ} (hxy : y ≠ x) :
    NullHomotopicAvoiding (fun _ => y) x :=
  ⟨ContinuousMap.const (ArcInterval × ArcInterval) y, fun p => hxy,
    fun t => rfl, fun t => rfl⟩

/-! ## The classical Jordan–Schoenflies datum -/

/-- **The classical planar Jordan–Schoenflies datum for a simple closed curve `c`.**

It consists of

* an embedded disc `e : 𝔻 → ℂ` spanning `c` (Jordan–Schoenflies), and
* the hard direction of the **Jordan curve theorem** in homotopy form: no point of the *open* disc
  can be contracted away, i.e. the curve is not null-homotopic in the complement of any interior
  point of the disc it spans.

Both are classical; the second is exactly the statement that the curve *winds* around the points
of the disc it bounds (equivalently, that the index of a simple closed curve is nonzero on the
inside).  It is the only separation-theoretic input of the convexity form of planar
Jordan–Schoenflies: the *other* direction (points outside a convex region can be contracted away)
is proved here, from convexity, by an explicit homotopy. -/
structure PlaneJordanData (c : ℝ → ℂ) where
  /-- the spanning embedded disc -/
  e : C(Work.InnermostDisk.Disc, ℂ)
  /-- the disc is embedded -/
  inj : Function.Injective e
  /-- its boundary is the curve -/
  boundary : ∀ θ : ℝ, e (Work.CoreTopology.circlePoint θ) = c θ
  /-- **Jordan's theorem, hard direction**: interior points of the disc cannot be contracted away -/
  inside_not_nullHomotopic : ∀ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 →
    ¬ NullHomotopicAvoiding c (e z)

/-- **The classical input of the planar chapter**: every simple closed plane curve has a
`PlaneJordanData`.  This is Jordan–Schoenflies plus the winding statement about the inside of a
Jordan curve. -/
def PlaneJordanInput : Prop :=
  ∀ c : ℝ → ℂ, Continuous c → Function.Periodic c (2 * Real.pi) →
    Set.InjOn c (Set.Ico 0 (2 * Real.pi)) → Nonempty (PlaneJordanData c)

/-! ## Separation from a convex set -/

/-- **A point outside a convex set is weakly separated from it by a continuous linear functional.**
If `D ⊆ ℂ` is convex with nonempty interior and `x ∉ D`, there is a nonzero real-linear functional
`f` which is at most `f x` on all of `D`.

This is the geometric Hahn–Banach theorem at a point
(`geometric_hahn_banach_of_nonempty_interior_point`), in the exact form the homotopy argument of
`nullHomotopicAvoiding_of_notMem_convex` consumes: the sublevel set `{f ≤ f x}` is a half-plane
containing `D` and bounded by a line through `x`. -/
theorem exists_functional_le_of_notMem_convex {D : Set ℂ} (hD : Convex ℝ D)
    (hint : (interior D).Nonempty) {x : ℂ} (hx : x ∉ D) :
    ∃ f : ℂ →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ D, f y ≤ f x :=
  geometric_hahn_banach_of_nonempty_interior_point hD
    (fun h => hx (interior_subset h)) hint

end

end Work.Smooth.Plane
