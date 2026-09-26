import Mathlib
import ChallengeDeps
import Submission.Box
import Submission.Work.CoreTopology.All
import Submission.Work.InnermostDisk.All
import Submission.Work.Topology.SphereSlicing.All

/-!
# `Work.Topology.Classical` — the classical topology that Mathlib is missing

This is the chapter that supplies — or, for the two classical theorems of geometric topology
which are missing from Mathlib and are not built here, *isolates as named hypotheses and reduces
to* — the input

```
Work.Topology.SphereSlicing.ClassicalInput P = SliceInput P ∧ CleanOneCurve P
```

for the tori `P = Work.CoreTopology.ParamTorus.mapHomeomorph ψ` of Pardon's theorem
(Ann. of Math. **174** (2011), Theorem 1.1), and hence Pardon's Lemma 4.2 at the boundary of the
box, `Work.Topology.SphereSlicing.mustbeinessentialBox_of_classicalInput_standard`.

The two halves of `ClassicalInput P` are:

* `SliceInput P` — a sphere `S` *in general position* with respect to the torus `F = P.carrier`
  is sliced by `F` into finitely many simple closed curves, each of which bounds an embedded disc
  inside `S` whose interior is open in `S`, and these discs are nested;
* `CleanOneCurve P` — the single cut-and-paste of Pardon's second innermost argument.

Both rest on classical theorems of geometric topology which Mathlib does not have (Mathlib has no
Jordan curve theorem at all):

* **Jordan–Schoenflies in `S²`** — a simple closed curve in the round sphere separates it into two
  closed discs meeting along the curve;
* **standard position of finitely many pairwise disjoint Jordan curves in `S²`** — their discs can
  be chosen so that they are nested (equivalently, the curves admit a consistent choice of sides;
  for a *finite* family this is the usual "choose the side not containing a point of the complement
  of the union of the curves"), which is what makes the innermost argument work;
* **Alexander's theorem in `ℝ³` with isotopy extension** — an embedded 2-sphere in `ℝ³` bounds a
  ball, so a disc can be pushed through it; this is the cut-and-paste.

These are isolated here as the propositions

* `Work.Topology.Classical.JordanSchoenfliesSphere` (this file), whose conclusion for a single
  family on a single set is packaged as the structure `Work.Topology.Classical.SchoenfliesData`;
* `Work.Topology.Classical.PushThroughInnermost` (this file), which is itself the conjunction of the
  two more primitive classical inputs `Work.Topology.Classical.InnermostCurveExists` (Jordan
  separation inside the disc: an innermost intersection curve exists) and
  `Work.Topology.Classical.CutsAlongSubdisc` (the surgery: Alexander's theorem plus isotopy
  extension); see `PushThrough.lean`.

Their conjunction is `Work.Topology.Classical.ClassicalTopology` (and
`Work.Topology.Classical.classicalTopology_of_decomposed` builds it from the primitive facts).  The
reductions

```
Work.Topology.Classical.sliceInput_standard_of_jordanSchoenflies
Work.Topology.Classical.cleanOneCurve_of_pushThroughInnermost
```

(`SliceInput.lean`, `cleanOneCurve_of_pushThroughInnermost.lean`) and the assembly
(`Assembly.lean`) are *proved*, so `ClassicalTopology → ClassicalInput standard →
ClassicalInput (mapHomeomorph ψ)` and everything downstream of Pardon's Lemma 4.2 becomes
unconditional in these classical facts alone.  Everything derived from the hypotheses — the
single-curve Jordan–Schoenflies theorem (`jordanSchoenflies_single`), the literal "the curve bounds
a disc whose interior misses it" (`bounds_disc_interior_disjoint`), Jordan separation
(`separation_of_schoenfliesData`, `isPreconnected_openDiscs_of_schoenfliesData`), the nesting of
the discs (`nested_discs_of_schoenfliesData`, `nestRel_trans_of_schoenfliesData`), the existence of
an innermost curve (`exists_innermost_of_schoenfliesData`), the non-emptiness of the complement of
finitely many disjoint Jordan curves (`exists_notMem_range_of_jordanSchoenflies`) and the transport
of the conclusion to an arbitrary embedded sphere or to the box boundary
(`schoenfliesData_of_jordanSchoenflies`, `nonempty_schoenfliesData_of_embeddedSphere`,
`nonempty_schoenfliesData_BoxSphere`) — is in the other modules of this directory.  See
`Submission/Work/Topology/Classical/README.md`.

## The exact shape of the two hypotheses

`JordanSchoenfliesSphere` is stated for the **round** unit sphere `RoundSphere = Metric.sphere 0 1`
(not for an arbitrary embedded sphere — the transport to an arbitrary sphere `S` along the
homeomorphism `Metric.sphere 0 1 ≃ₜ S` supplied by `IsEmbeddedSphere S` is *proved* here,
`exists_homeomorph_roundSphere.lean`, and the assembly *proves* `SliceInput standard` from it).  Its clauses are,
curve by curve:

* the two complementary closed discs `e i` and `e' i` have the curve as common boundary, in the
  given parametrisation (`e i (circlePoint θ) = c i θ`);
* they are embedded, their images cover the sphere and meet exactly in the curve (Jordan–Schoenflies
  proper);
* the image of the *open* disc is open in the sphere (the separation statement proper, "the
  bounded component of `S² ∖ c` is open");
* and the discs are *nested*, witnessed by the rank (`rank j < rank i` when the curve `j` meets the
  interior of the disc of `i`): the standard position of finitely many pairwise disjoint Jordan
  curves on `S²`.

## Conventions

* `R3 = LeanEval.KnotTheory.PardonDistortion.R3 = EuclideanSpace ℝ (Fin 3)`;
* `Disc = Work.InnermostDisk.Disc = Metric.closedBall (0 : ℂ) 1` is the model 2-disc, with
  boundary circle `Work.CoreTopology.circlePoint`;
* `Work.CoreTopology.ParamTorus` is a parametrised embedded torus, `standard` the standard torus
  of revolution with major radius `2` and minor radius `1`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.Classical

noncomputable section

/-! ## The round sphere and Jordan curves on it -/

/-- The round unit `2`-sphere `S² ⊆ ℝ³`, the model sphere of the Jordan–Schoenflies theorem. -/
def RoundSphere : Set R3 := Metric.sphere (0 : R3) 1

@[simp] theorem mem_RoundSphere {x : R3} : x ∈ RoundSphere ↔ ‖x‖ = 1 := by
  simp [RoundSphere]

theorem RoundSphere_eq_sphere : RoundSphere = Metric.sphere (0 : R3) 1 := rfl

/-- A **simple closed curve** on a subset `A ⊆ ℝ³`: a continuous, `2π`-periodic map whose image
lies in `A` and which is injective on one period `[0, 2π)`.  This is the shape of curve for which
the Jordan–Schoenflies theorem is stated. -/
def IsJordanCurveOn (A : Set R3) (c : ℝ → R3) : Prop :=
  (∀ t : ℝ, c t ∈ A) ∧ Continuous c ∧ Function.Periodic c (2 * Real.pi) ∧
    Set.InjOn c (Set.Ico 0 (2 * Real.pi))

/-- A simple closed curve on the round sphere. -/
def IsJordanCurveRound (c : ℝ → R3) : Prop := IsJordanCurveOn RoundSphere c

/-- **Jordan–Schoenflies on the round `2`-sphere, with standard position of finitely many
pairwise disjoint curves.**

Let `c i` (`i` in a finite type) be pairwise disjoint simple closed curves on the round unit sphere
`RoundSphere ⊆ ℝ³`.  Then there are, for each `i`, two embedded closed discs `e i` and `e' i` with
common boundary the curve `c i` (in the given parametrisation), covering the sphere and meeting
exactly in the curve, with the image of the open disc open in the sphere, and a **rank** `rank`
witnessing that the discs are nested (if the curve `j` meets the interior of the disc of `i`, then
`rank j < rank i`).

Every clause is a classical theorem of geometric topology:

* "two embedded discs with common boundary covering `S²`" and "the bounded component of `S² ∖ c` is
  open" are the **Jordan–Schoenflies theorem** in the `2`-sphere;
* the rank clause is the **standard position of finitely many pairwise disjoint Jordan curves on
  `S²`**: their chosen discs are nested (equivalently, the curves admit a *consistent* choice of
  side, which for a finite family one obtains from a point of the complement of their union; the
  relation "the curve `j` lies in the disc of `i`" is then a strict partial order, and a rank
  decreasing along it exists).

This is the sharpest form of the classical slicing input which the present chapter isolates: it
mentions neither a torus nor transversality, only the round sphere and Jordan curves on it.  From it
`Work.Topology.Classical.sliceInput_standard_of_jordanSchoenflies` *proves* the slicing of every
embedded sphere in general position by the standard torus of revolution. -/
def JordanSchoenfliesSphere : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → ℝ → R3),
    (∀ i : ι, IsJordanCurveRound (c i)) →
    (Pairwise fun i j : ι => Disjoint (Set.range (c i)) (Set.range (c j))) →
    ∃ (e e' : ι → C(Disc, R3)) (rank : ι → ℕ),
      (∀ i : ι, Function.Injective (e i)) ∧
      (∀ i : ι, Function.Injective (e' i)) ∧
      (∀ i : ι, ∀ θ : ℝ, e i (circlePoint θ) = c i θ) ∧
      (∀ i : ι, ∀ θ : ℝ, e' i (circlePoint θ) = c i θ) ∧
      (∀ i : ι, ∀ z : Disc, e i z ∈ RoundSphere) ∧
      (∀ i : ι, ∀ z : Disc, e' i z ∈ RoundSphere) ∧
      (∀ i : ι, IsOpen {x : RoundSphere |
        ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e i z = (x : R3)}) ∧
      (∀ i : ι, IsOpen {x : RoundSphere |
        ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e' i z = (x : R3)}) ∧
      (∀ i : ι, Set.range (e i) ∪ Set.range (e' i) = RoundSphere) ∧
      (∀ i : ι, Set.range (e i) ∩ Set.range (e' i) = Set.range (c i)) ∧
      (∀ i j : ι, (∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e i z ∈ Set.range (c j)) →
        rank j < rank i)

/-! ## The conclusion of Jordan–Schoenflies, packaged

The structure `SchoenfliesData` collects the conclusion of `JordanSchoenfliesSphere` for a single
family of curves on a single set `A ⊆ ℝ³` (in practice: an embedded sphere, e.g. the round sphere
or the box boundary).  Its clauses are exactly the clauses of `JordanSchoenfliesSphere` with
`RoundSphere` replaced by `A`; packaging them lets the transport along a homeomorphism
`RoundSphere ≃ₜ A` be stated and used without repeating a dozen clauses, see
`Work.Topology.Classical.schoenfliesData_of_jordanSchoenflies` and its corollaries
`nonempty_schoenfliesData_of_embeddedSphere` and `nonempty_schoenfliesData_BoxSphere`. -/
structure SchoenfliesData (A : Set R3) (ι : Type) [Fintype ι] (c : ι → ℝ → R3) where
  /-- one of the two embedded discs bounded by `c i` -/
  e : ι → C(Disc, R3)
  /-- the other one -/
  e' : ι → C(Disc, R3)
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
  /-- the first disc is contained in `A` -/
  mem : ∀ i : ι, ∀ z : Disc, e i z ∈ A
  /-- the second disc is contained in `A` -/
  mem' : ∀ i : ι, ∀ z : Disc, e' i z ∈ A
  /-- the bounded component of `A ∖ c i` is open in `A` -/
  open_interior : ∀ i : ι,
    IsOpen {x : A | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e i z = (x : R3)}
  /-- likewise for the other side -/
  open_interior' : ∀ i : ι,
    IsOpen {x : A | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e' i z = (x : R3)}
  /-- the two discs cover `A` -/
  cover : ∀ i : ι, Set.range (e i) ∪ Set.range (e' i) = A
  /-- they meet exactly in the curve -/
  meet : ∀ i : ι, Set.range (e i) ∩ Set.range (e' i) = Set.range (c i)
  /-- the discs are nested -/
  nested : ∀ i j : ι, (∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ e i z ∈ Set.range (c j)) → rank j < rank i

/-! ## Alexander's theorem (recorded for the archive) -/

/-- **Alexander's theorem for an embedded `2`-sphere in `ℝ³`**, in the form in which the
cut-and-paste uses it: an embedded `2`-sphere bounds a *ball*, i.e. a compact region `K` whose
frontier is the sphere and which is homeomorphic to the closed unit ball.

This proposition is recorded here for completeness, because it is the separation theorem behind
`PushThroughInnermost` below.  The cut-and-paste also needs the isotopy extension theorem (to
push the disc through the ball that `K` provides, keeping the remaining part of the disc fixed),
and it is the *output* of that pair of theorems — a new embedded disc with the same boundary
whose interior meets `F` only along the curves other than the innermost one — which is what the
argument actually consumes, so `PushThroughInnermost` is the hypothesis which
`Work.Topology.Classical.cleanOneCurve_of_pushThroughInnermost` reduces `CleanOneCurve` to.
Nothing in this chapter depends on this proposition; it documents what is being assumed. -/
def AlexanderSphereTheorem : Prop :=
  ∀ S : Set R3, IsEmbeddedSphere S →
    ∃ K : Set R3, IsCompact K ∧ S = frontier K ∧
      Nonempty (K ≃ₜ Metric.closedBall (0 : R3) 1)

/-! ## The cut-and-paste -/

/-- **The single cut-and-paste of Pardon's second innermost argument.**

Let `D` be an embedded disc in `ℝ³` whose boundary `α` is a simple closed curve of the torus
`F = P.carrier` and whose interior meets `F` only along the finite family of pairwise disjoint
inessential simple curves `D.curves`.  If that family is nonempty then there is a curve `γ = D.curves
j` and an embedded disc `e'` in `ℝ³`, with the **same boundary** `α`, such that

* every *other* curve `D.curves i` (`i ≠ j`) is contained in `e'`, and
* every point of `e'` in the *interior* of the disc which lies on `F` lies on one of those other
  curves.

So the intersection curve `γ` has been eliminated: the new disc is embedded, has the same boundary,
and its interior meets `F` only along the old curves other than `γ`.  (Pardon: "considering such an
inessential curve which is innermost in `F`, it is easy to see that we can modify `D` so as to
eliminate this intersection, while keeping `D` embedded.")

Classically one takes `γ` innermost in `D`, so that it bounds a sub-disc `D_γ` whose interior misses
`F`; being inessential, `γ` also bounds a disc `E ⊆ F`; the union `S = D_γ ∪ E` is an embedded
`2`-sphere in `ℝ³`, which by **Alexander's theorem** bounds a ball, and the part of `D` inside that
ball is pushed through `S` (by the **isotopy extension theorem**), removing `γ` and leaving the disc
embedded with the same boundary.  The two named classical inputs of this step are therefore
Alexander's theorem and isotopy extension.

`Work.Topology.Classical.cleanOneCurve_of_pushThroughInnermost` *proves* `CleanOneCurve P` from
this proposition, by taking the new `SliceDisc` to be `e'` with index type the complement of `j` in
`D.ι`. -/
def PushThroughInnermost (P : ParamTorus) : Prop :=
  ∀ D : Work.Topology.SphereSlicing.SliceDisc P, 0 < Fintype.card D.ι →
    ∃ (j : D.ι) (e' : C(Disc, R3)),
      Function.Injective e' ∧
      (∀ θ : ℝ, e' (circlePoint θ) = D.α.γ θ) ∧
      (∀ i : D.ι, i ≠ j → Set.range (D.curves i).γ ⊆ Set.range e') ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → e' z ∈ P.carrier →
        ∃ i : D.ι, i ≠ j ∧ e' z ∈ Set.range (D.curves i).γ)

/-! ## Decomposition of the cut-and-paste into its two classical ingredients -/

/-- **Pardon's "innermost in the surface" step.**  A slice disc with at least one intersection
curve has an intersection curve which bounds a *sub-disc* `f` of the disc, with the following
properties: `f` is embedded; its boundary is the curve, in the given parametrisation; the interior
of `f` misses the surface `F`; and no other intersection curve meets the *open* sub-disc
`f '' {z | ‖z‖ < 1}`.

This is the classical "take an intersection curve innermost in the disc": the curves in the disc
are finitely many pairwise disjoint Jordan curves, so one of them bounds a sub-disc containing no
other curve, and the Jordan separation theorem inside the disc identifies its interior as a region
disjoint from `F` (the other curves being the only points of `F ∩ int D`).  It is the first of the
two ingredients of `PushThroughInnermost`, see
`Work.Topology.Classical.pushThroughInnermost_of_innermostCurveExists_of_cutsAlongSubdisc`. -/
def InnermostCurveExists (P : ParamTorus) : Prop :=
  ∀ D : Work.Topology.SphereSlicing.SliceDisc P, 0 < Fintype.card D.ι →
    ∃ (j : D.ι) (f : C(Disc, R3)),
      Function.Injective f ∧
      (∀ θ : ℝ, f (circlePoint θ) = (D.curves j).γ θ) ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → f z ∉ P.carrier) ∧
      Set.range f ⊆ Set.range D.e ∧
      (∀ i : D.ι, i ≠ j →
        Disjoint (Set.range (D.curves i).γ) (f '' {z : Disc | ‖(z : ℂ)‖ < 1}))

/-- **The surgery half of Pardon's cut-and-paste** — the piece of **Alexander's theorem** together
with **isotopy extension** that the argument consumes.  Given a slice disc `D` and an innermost
sub-disc `f` of it (embedded, spanning `D.curves j`, whose interior misses `F` and which no other
intersection curve meets), there is an embedded disc `e'` with the *same boundary* as `D` such that

* every intersection curve of `D` other than `D.curves j` is contained in `e'`, and
* every point of `e'` in the open disc lying on `F` lies on one of those other curves.

Classically: `f` and the disc `E ⊆ F` that the inessential curve `D.curves j` bounds form an
embedded `2`-sphere, which by Alexander's theorem bounds a ball; the part of `D` inside that ball
is pushed through the sphere by an ambient isotopy fixing the boundary, eliminating exactly the
curve `D.curves j` and no other.  The condition that the remaining curves lie in `e'` is the
Jordan separation statement that they lie outside the ball cut off by `f ∪ E`. -/
def CutsAlongSubdisc (P : ParamTorus) : Prop :=
  ∀ (D : Work.Topology.SphereSlicing.SliceDisc P) (j : D.ι) (f : C(Disc, R3)),
    Function.Injective f →
    (∀ θ : ℝ, f (circlePoint θ) = (D.curves j).γ θ) →
    (∀ z : Disc, ‖(z : ℂ)‖ < 1 → f z ∉ P.carrier) →
    Set.range f ⊆ Set.range D.e →
    (∀ i : D.ι, i ≠ j →
      Disjoint (Set.range (D.curves i).γ) (f '' {z : Disc | ‖(z : ℂ)‖ < 1})) →
    ∃ e' : C(Disc, R3),
      Function.Injective e' ∧
      (∀ θ : ℝ, e' (circlePoint θ) = D.α.γ θ) ∧
      (∀ i : D.ι, i ≠ j → Set.range (D.curves i).γ ⊆ Set.range e') ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → e' z ∈ P.carrier →
        ∃ i : D.ι, i ≠ j ∧ e' z ∈ Set.range (D.curves i).γ)

/-! ## The single packaged classical input -/

/-- **The classical input of this chapter**: the Jordan–Schoenflies theorem together with the
standard position of finitely many disjoint Jordan curves on the round sphere, and the cut-and-paste
(which rests on Alexander's theorem and isotopy extension) for the standard torus of revolution.

This is the *only* thing assumed in this directory; everything else
(`SliceInput standard`, `CleanOneCurve standard`, hence `ClassicalInput standard`, hence Pardon's
Lemma 4.2 at the box boundary for every torus `ψ(F_standard)`) is proved from it, see
`Work.Topology.Classical.Assembly`. -/
def ClassicalTopology : Prop :=
  JordanSchoenfliesSphere ∧ PushThroughInnermost standard

end

end Work.Topology.Classical
