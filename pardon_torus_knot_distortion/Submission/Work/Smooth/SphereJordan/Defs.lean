import Mathlib
import ChallengeDeps
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Topology.Classical.All
import Submission.Work.InnermostDisk.All
import Submission.Work.Topology.SphereSlicing.All

/-!
# `Work.Smooth.SphereJordan` — the sphere-side and surface-side classical inputs of Pardon's
theorem, derived from the *planar* Jordan–Schoenflies theorem

This chapter closes the two classical inputs which the delivered chapters
`Submission/Work/Topology/Classical` and `Submission/Work/InnermostDisk` isolate as hypotheses,
by deriving them from the **planar** Jordan–Schoenflies theorem (the theorem isolated by the
sibling chapter `Submission/Work/Smooth/Jordan` as `Work.Smooth.Jordan.PlaneJordanSchoenflies` /
`SchoenfliesInput`, and in flight in `Submission/Work/Smooth/JordanSeparation`):

* **`Work.Topology.Classical.JordanSchoenfliesSphere`** — Jordan–Schoenflies on the round sphere
  together with the standard position (nesting) of finitely many pairwise disjoint Jordan curves;
* **the cut-and-paste** `Work.InnermostDisk.CleansDiscs P` of Pardon's second innermost argument
  for the tori `P = Work.CoreTopology.ParamTorus.mapHomeomorph ψ` of the challenge.

## The route

The proof is carried out on the **Riemann sphere** `RiemannSphere = OnePoint ℂ = ℂ ∪ {∞}`, for
which the *plane* is a literal subset (the finite part) and the planar theorem applies verbatim to
every curve missing `∞`; at the very end everything is transferred to the round sphere
`Metric.sphere (0 : ℝ³) 1` along Mathlib's stereographic homeomorphism
`onePointEquivSphereOfFinrankEq`.

The mathematical content, in the order in which it is used:

1. **`PlaneHypothesis`** — the planar Jordan–Schoenflies theorem, taken as the hypothesis of the
   chapter (this is exactly the sibling chapter's `Work.Smooth.Jordan.ClassicalInput`); the
   *planar* proof itself is not repeated here.
2. **The planar two-disc theorem** (`PlaneTwoDiscs`): a simple closed curve `γ` in `ℂ` bounds
   **two** complementary discs in `ℂ ∪ {∞}`, not just the bounded one supplied by Jordan–Schoenflies.
   This is where the classical argument lives: the bounded side is a disc by the planar theorem,
   and the closure of the *unbounded* side together with `∞` is the image of a disc obtained by
   inverting in a point of the bounded side: for `z₀ ∈ V`, the curve
   `γ̃(t) = (γ(t) - z₀)⁻¹` is a simple closed plane curve, the inversion `φ(w) = (w - z₀)⁻¹` maps the
   unbounded side of `γ` onto the *bounded* side of `γ̃` (up to the single point `0`) and the bounded
   side of `γ` into the unbounded side of `γ̃`; hence the planar spanning disc of `γ̃`, pulled back
   along `φ`, spans the closure of the unbounded side of `γ` in `ℂ ∪ {∞}`.
3. **Schoenflies on the Riemann sphere** (`TwoDiscs`): for *any* simple closed curve, first find a
   point of the sphere off the curve (`curve_misses_point`, proved from scratch: the image of an
   injective continuous map from a compact interval into `ℂ` has empty interior, and a finite union
   of such images has empty interior), then transport the planar theorem along the chart at that
   point (a Möbius transformation of `ℂ ∪ {∞}`).
4. **Standard position / nesting** (`FamilyData`): for a finite family of pairwise disjoint simple
   closed curves on the sphere, a point off their union exists (the union of finitely many
   nowhere dense closed sets is nowhere dense), each curve is given the disc that does *not*
   contain it, and the relation "the curve `i` lies inside the disc of `j`" is proved to be a
   strict partial order; `Work.Topology.SphereSlicing.exists_rank_of_strict_order` then produces
   the rank. This proves `JordanSchoenfliesRiemannSphere`.
5. **Transfer to the round sphere**: `JordanSchoenfliesRiemannSphere` implies
   `Work.Topology.Classical.JordanSchoenfliesSphere` (the *stated* Prop), and hence, by the
   delivered lemmas of `Work.Smooth.Jordan` and `Work.Topology.Classical`,
   `Work.Smooth.Jordan.SchoenfliesOnInput A` for every `A` homeomorphic to the round sphere — in
   particular for the box boundary `∂PBox s c σ`.
6. **The cut-and-paste** (`Work.Smooth.SphereJordan.Pasting`,
   `Work.Smooth.SphereJordan.PastingDerive`, `Work.Smooth.SphereJordan.PastingAssembly`): Pardon's
   second innermost argument for the local model `Work.Topology.SphereSlicing.SliceDisc`: the
   innermost sub-disc of a slice disc is modified — discarding a collar of the innermost curve,
   capping the truncated outer annulus with the push-off of the surface disc that curve bounds —
   so that the intersection curve disappears while the disc stays embedded with the same boundary.
   The construction is *proved* here from named classical inputs (`AnnulusSchoenflies`, the annulus
   form of Schoenflies; `SurfaceDiscPushOff`, the push-off of a surface disc) together with the
   position hypothesis `CurvesInterior` on the slice discs (constructive route) or Pardon's
   `PinchedPushThrough` (which needs Alexander's theorem and isotopy extension); see
   `Submission/Work/Smooth/SphereJordan/README.md`.

## Main definitions

* `RiemannSphere` — the one-point compactification `ℂ ∪ {∞}`;
* `IsSimpleClosedCurve c` — a continuous, `2π`-periodic, injective-on-one-period curve
  `ℝ → RiemannSphere`;
* `TwoDiscs c` — **two complementary embedded discs** in the Riemann sphere bounded by `c`:
  `e`, `e' : 𝔻 → ℂ ∪ {∞}` injective, with boundary `c` in the given parametrisation, images covering
  the sphere and meeting exactly in the curve, and the image of the *open* disc open in the sphere
  (Jordan separation);
* `FamilyData c` — the standard position of a finite family of pairwise disjoint simple closed
  curves: two discs per curve as above, plus a nesting rank;
* `PlaneHypothesis` — the planar Jordan–Schoenflies theorem (the hypothesis of the chapter).

## Main results

See `Submission/Work/Smooth/SphereJordan/README.md` for the full table.  The two headline results
for a caller are

* `Work.Smooth.SphereJordan.jordanSchoenfliesSphere` : `Work.Topology.Classical.JordanSchoenfliesSphere`,
* `Work.Smooth.SphereJordan.cutsAlongSubdisc_of_props` :
  `Work.Topology.Classical.CutsAlongSubdisc P` for every parametrised torus `P`, from the planar
  theorem and the named inputs `AnnulusSchoenflies`, `SurfaceDiscPushOff` (together with
  `CurvesInterior` or `PinchedPushThrough`);
* `Work.Smooth.SphereJordan.cleansDiscsAll_of_props` : `Work.InnermostDisk.CleansDiscs P` for every
  `P = ParamTorus.mapHomeomorph ψ.toHomeomorph` of the challenge.

Nothing outside `Submission/Work/Smooth/SphereJordan/` is modified.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## The Riemann sphere -/

/-- The **Riemann sphere**: the one-point compactification `ℂ ∪ {∞}` of the plane.  Its finite part
is (the range of the coercion of) `ℂ`, which makes the planar Jordan–Schoenflies theorem of the
sibling chapter applicable verbatim to every curve missing `∞`. -/
abbrev RiemannSphere : Type := OnePoint ℂ

/-- The model closed `2`-disc `𝔻 = {z : ℂ | ‖z‖ ≤ 1}` (definitionally the `Work.Smooth.Jordan.Disc`
of the sibling chapter and the `Work.InnermostDisk.Disc` of the innermost-disc chapter). -/
abbrev Disc : Type := Metric.closedBall (0 : ℂ) 1

/-- The boundary point `e^{iθ}` of the model disc. -/
abbrev circlePoint : ℝ → Disc := Work.Smooth.Jordan.circlePoint

/-- The point `∞` of the Riemann sphere. -/
abbrev infty : RiemannSphere := OnePoint.infty

/-- Mathlib's stereographic homeomorphism `ℂ ∪ {∞} ≃ₜ S²` (the one-point compactification of a
real vector space of dimension `2` is the round `2`-sphere of `ℝ³`). -/
def riemannSphereHomeomorph : RiemannSphere ≃ₜ Work.Smooth.Jordan.RoundSphere :=
  onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)

/-! ## Simple closed curves on the Riemann sphere -/

/-- A **simple closed curve on the Riemann sphere**: continuous, `2π`-periodic and injective on one
period `[0, 2π)`.  This is the exact analogue of `Work.Smooth.Jordan.IsSimpleClosedCurveOn` (and of
`Work.Topology.Classical.IsJordanCurveOn`), stated for the sphere `ℂ ∪ {∞}` rather than for a subset
of `ℝ³`. -/
def IsSimpleClosedCurve (c : ℝ → RiemannSphere) : Prop :=
  Continuous c ∧ Function.Periodic c (2 * Real.pi) ∧ Set.InjOn c (Set.Ico 0 (2 * Real.pi))

theorem IsSimpleClosedCurve.continuous {c : ℝ → RiemannSphere} (h : IsSimpleClosedCurve c) :
    Continuous c := h.1

theorem IsSimpleClosedCurve.periodic {c : ℝ → RiemannSphere} (h : IsSimpleClosedCurve c) :
    Function.Periodic c (2 * Real.pi) := h.2.1

theorem IsSimpleClosedCurve.injOn {c : ℝ → RiemannSphere} (h : IsSimpleClosedCurve c) :
    Set.InjOn c (Set.Ico 0 (2 * Real.pi)) := h.2.2

/-! ## Two complementary discs bounded by a curve -/

/-- **Jordan–Schoenflies on the Riemann sphere, in the two-disc form.**

A simple closed curve `c` of the Riemann sphere is the common boundary of two embedded closed discs
`e`, `e'`: both are continuous injections of the model disc `𝔻`, their boundary circle maps to `c`
*in the given parametrisation*, their images cover the sphere and meet exactly in the curve, and the
image of the *open* disc is open in the sphere.

The last clause is the Jordan *separation* statement proper ("the bounded component of the
complement of `c` is open"), and it is what makes the nesting argument in `Family.lean` work. -/
structure TwoDiscs (c : ℝ → RiemannSphere) where
  /-- the curve is a simple closed curve -/
  simple : IsSimpleClosedCurve c
  /-- one of the two discs -/
  e : C(Disc, RiemannSphere)
  /-- the other one -/
  e' : C(Disc, RiemannSphere)
  /-- the first disc is embedded -/
  inj : Function.Injective e
  /-- the second disc is embedded -/
  inj' : Function.Injective e'
  /-- the boundary of the first disc is the curve -/
  boundary : ∀ θ : ℝ, e (circlePoint θ) = c θ
  /-- the boundary of the second disc is the curve -/
  boundary' : ∀ θ : ℝ, e' (circlePoint θ) = c θ
  /-- the image of the open disc of the first disc is open in the sphere -/
  open_interior : IsOpen {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e z = x}
  /-- likewise for the second disc -/
  open_interior' : IsOpen {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e' z = x}
  /-- the two discs cover the sphere -/
  cover : Set.range e ∪ Set.range e' = Set.univ
  /-- they meet exactly in the curve -/
  meet : Set.range e ∩ Set.range e' = Set.range c

/-! ## Standard position of a finite family of pairwise disjoint curves -/

/-- **The standard position of a finite family of pairwise disjoint simple closed curves on the
Riemann sphere**: two complementary discs per curve, together with a *nesting rank* — a curve which
meets the interior of the disc of another has smaller rank.  This is exactly
`Work.Topology.Classical.SchoenfliesData` for the sphere `ℂ ∪ {∞}`, together with the statement
(proved in `Family.lean`) that the rank exists as soon as the discs are chosen "not containing a
point off the union of the curves". -/
structure FamilyData {ι : Type} [Fintype ι] (c : ι → ℝ → RiemannSphere) where
  /-- one of the two discs bounded by each curve -/
  e : ι → C(Disc, RiemannSphere)
  /-- the other one -/
  e' : ι → C(Disc, RiemannSphere)
  /-- the nesting rank -/
  rank : ι → ℕ
  /-- the first disc is embedded -/
  inj : ∀ i : ι, Function.Injective (e i)
  /-- the second disc is embedded -/
  inj' : ∀ i : ι, Function.Injective (e' i)
  /-- the boundary of the first disc is the curve, in the given parametrisation -/
  boundary : ∀ i : ι, ∀ θ : ℝ, e i (circlePoint θ) = c i θ
  /-- the boundary of the second disc is the curve, in the given parametrisation -/
  boundary' : ∀ i : ι, ∀ θ : ℝ, e' i (circlePoint θ) = c i θ
  /-- the interior of the first disc is open in the sphere -/
  open_interior : ∀ i : ι,
    IsOpen {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e i z = x}
  /-- likewise for the second disc -/
  open_interior' : ∀ i : ι,
    IsOpen {x : RiemannSphere | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e' i z = x}
  /-- the two discs of a curve cover the sphere -/
  cover : ∀ i : ι, Set.range (e i) ∪ Set.range (e' i) = Set.univ
  /-- they meet exactly in the curve -/
  meet : ∀ i : ι, Set.range (e i) ∩ Set.range (e' i) = Set.range (c i)
  /-- the discs are nested -/
  nested : ∀ i j : ι, (∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e i z ∈ Set.range (c j)) → rank j < rank i

/-! ## The classical input of the chapter -/

/-- **The planar Jordan–Schoenflies theorem** — the hypothesis of this chapter, exactly the
`Work.Smooth.Jordan.ClassicalInput` / `SchoenfliesInput` of the sibling chapter: every simple closed
plane curve bounds an embedded disc whose image is the closure of the bounded side of the curve
(and the separation of the plane by the curve is part of the datum).  The sibling subproject
`Submission/Work/Smooth/JordanSeparation` proves this. -/
def PlaneHypothesis : Prop :=
  ∀ c : Work.Smooth.Jordan.PlaneCurve,
    Work.Smooth.Jordan.PlaneCurve.IsSimple c → Nonempty (Work.Smooth.Jordan.PlaneSchoenflies c)

/-- The planar hypothesis is exactly the sibling chapter's `ClassicalInput`. -/
theorem planeHypothesis_iff_classicalInput :
    PlaneHypothesis ↔ Work.Smooth.Jordan.ClassicalInput := Iff.rfl

/-- **Jordan–Schoenflies for one simple closed curve on the Riemann sphere.** -/
def SchoenfliesRiemannSphere : Prop :=
  ∀ c : ℝ → RiemannSphere, IsSimpleClosedCurve c → Nonempty (TwoDiscs c)

/-- **Jordan–Schoenflies and standard position for a finite family of pairwise disjoint simple
closed curves on the Riemann sphere.** -/
def JordanSchoenfliesRiemannSphere : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → ℝ → RiemannSphere),
    (∀ i : ι, IsSimpleClosedCurve (c i)) →
    (Pairwise fun i j : ι => Disjoint (Set.range (c i)) (Set.range (c j))) →
    Nonempty (FamilyData c)

end

end Work.Smooth.SphereJordan
