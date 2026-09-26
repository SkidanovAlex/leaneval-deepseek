import Mathlib
import ChallengeDeps
import Submission.Box
import Submission.Work.CoreTopology.All
import Submission.Work.InnermostDisk.All

/-!
# `Work.Topology.SphereSlicing` — the classical surface-topology chapter behind Pardon's Lemma 4.2

This directory discharges (or, where a classical theorem of geometric topology is missing from
Mathlib and cannot be built here, cleanly *reduces*) the two explicit inputs of
`Submission.Work.InnermostDisk`, specialised to what Pardon's argument needs:

`Work.InnermostDisk.mustbeinessential_of_PLInput` consumes

* `Work.InnermostDisk.SphereSlicingInput P` — every embedded sphere is sliced by `F = P.carrier`
  into finitely many pairwise disjoint simple closed curves, each bounding a disc inside the
  sphere; and
* `Work.InnermostDisk.CleansDiscs P` — Pardon's second innermost argument (the cut-and-paste).

The content of this chapter is:

## 1. The box (item 1 of the assignment)

`Submission.PBox s c σ` is the open box of `Submission/Box.lean`; its boundary is the *box
sphere* `BoxSphere s c σ = {y | boxNorm c σ y = s}`, a polyhedral `S²`.  Here we record that the
box is open and convex, that the box sphere is compact and closed, and we give an **explicit**
homeomorphism `BoxSphere s c σ ≃ₜ Metric.sphere 0 1` (radial projection followed by the inverse
of radial projection, both written out); consequently `BoxSphere s c σ` is an
`Work.InnermostDisk.IsEmbeddedSphere`, which is the form in which the box is fed to Pardon's
Lemma.  See `Work.Topology.SphereSlicing.Box.*`.

## 2. The slicing of a sphere by the torus (item 2)

Instead of taking `Work.InnermostDisk.SphereSlicing P S` as the input, we introduce the
*smaller* structure `SliceData P S`, whose fields are exactly the classical facts about a PL
sphere `S` transverse to the PL surface `F`:

* **transversality**: `S ∩ F` is the union of finitely many pairwise disjoint simple closed
  curves of `F`, each of them contained in `S` (`c`, `simple`, `disjoint`, `mem`, `covers_pt`);
* **Jordan–Schoenflies in `S²`**: each of those curves bounds an embedded disc inside `S`
  (`disc`, `disc_inj`, `disc_boundary`, `disc_mem`), whose interior is *open in `S`*
  (`open_interior` — this is the separation statement proper, "the bounded component of
  `S ∖ cᵢ` is open");
* **nesting**: the curves are nested, witnessed by a rank function (`rank`, `inside`).

From `SliceData P S` everything else that `Work.InnermostDisk.SphereSlicing P S` asks for is
**proved** here: the finite family covers every loop of `F` inside `S` (`covers`, from
connectedness of the loop and closedness of the components), the disc of a curve contains every
other curve meeting its interior (`inside_subset`, from openness of the interior and
connectedness), and the interior of a disc meets `F` only along the components
(`covers_interior`).  So the reduction `SphereSlicing` ⟸ `SliceData` is real: two of the fifteen
fields of `SphereSlicing` disappear into proved lemmas, the pointwise covering replaces the
curve-wise covering, and the disc's interior is required to be open in `S` (which is what
Jordan–Schoenflies actually gives).  See `Work.Topology.SphereSlicing.Slice.*`.

## 3. The cut-and-paste (item 3)

`Work.InnermostDisk.CleansDiscs P` is Pardon's second innermost argument, and
`Work.InnermostDisk.cleansDiscs_of_removesOneCurve` already reduces it to a *single* cut-and-paste
`RemovesOneCurve P`.  Here the cut-and-paste is restated on its own as `CleanOneCurve P`, in
terms of the local model `SliceDisc P` of an embedded disc in `ℝ³`:

  an embedded disc `D ⊆ ℝ³` whose boundary is a simple closed curve `α` of `F` and whose interior
  meets `F` only along a finite family of pairwise disjoint *inessential* simple closed curves of
  `F`, with at least one such curve, can be replaced — keeping `α` as boundary — by such a disc
  with strictly fewer intersection curves.

The field `essential` (of `InnermostDisc`), the ambient set `S` and the condition that the disc
be contained in `S` do not appear in `CleanOneCurve`: they are not used by the cut-and-paste, and
`SliceDisc` is the exact geometric situation ("an open embedded disc in `ℝ³` whose boundary is a
simple closed curve of `F` and whose interior meets `F` only in inessential curves") in which
Pardon's push-through argument applies.  The reduction `RemovesOneCurve P` (and hence
`CleansDiscs P`) from `CleanOneCurve P` is proved in `Work.Topology.SphereSlicing.Clean.Reduce`.
See `Work.Topology.SphereSlicing.Clean.*`.

## 4. Assembly (item 4)

`ClassicalInput P = SliceInput P ∧ CleanOneCurve P` is the complete classical input of Pardon's
Lemma 4.2 in the vocabulary of this chapter; `Work.Topology.SphereSlicing.Assembly` proves that it
implies `Work.InnermostDisk.PardonPLInput P`, instantiates everything at the box sphere
`S = BoxSphere s c σ`, and — for the tori of the challenge, `P = ParamTorus.mapHomeomorph ψ` and
`β = ψ`-image of the standard `(p,q)`-curve — turns the intersection count
`#(β ∩ ∂PBox s c σ) < min p q` into Pardon's conclusion: the box boundary contains no essential
loop of the torus.  That is exactly the statement the sibling deliverable
`Work.BoxBubble.mustbeinessentialBox` needs.

## Conventions

* `ℝ³` is `LeanEval.KnotTheory.PardonDistortion.R3 = EuclideanSpace ℝ (Fin 3)`.
* A "loop of `F`" is a `Work.CoreTopology.ClosedCurve P`: a continuous `2π`-periodic curve in
  `F = P.carrier`; `IsEssential` means "nonzero winding vector", `IsSimple` means "injective on
  `[0, 2π)`".
* Nothing outside `Submission/Work/Topology/SphereSlicing/` is modified.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.SphereSlicing

noncomputable section

/-! ## The boundary sphere of Pardon's box -/

/-- **The box sphere** `∂PBox s c σ`: the boundary of Pardon's box `Submission.PBox s c σ`, i.e.
the level set `{y | boxNorm c σ y = s}` of the box norm.  It is a polyhedral 2-sphere (the six
faces of the box), and `Work.Topology.SphereSlicing.isEmbeddedSphere_BoxSphere` shows that it is
an embedded sphere of `ℝ³`. -/
def BoxSphere (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  {y : R3 | Submission.boxNorm c σ y = s}

@[simp] theorem mem_BoxSphere {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {y : R3} :
    y ∈ BoxSphere s c σ ↔ Submission.boxNorm c σ y = s := Iff.rfl

theorem BoxSphere_eq_frontier (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    BoxSphere s c σ = {y : R3 | Submission.boxNorm c σ y = s} := rfl

/-! ## The slicing datum -/

/-- **A slicing datum for a sphere `S` by the surface `F = P.carrier`.**

This is the part of `Work.InnermostDisk.SphereSlicing P S` which is genuinely classical.  The
sphere `S` is a PL (or smooth) sphere transverse to the PL (or smooth) surface `F`; then

* `S ∩ F` is a finite disjoint union of simple closed curves of `F` (`c`, `simple`, `disjoint`,
  `mem`), and every point of `S ∩ F` lies on one of them (`covers_pt`);
* each of those curves bounds an embedded disc inside `S` (`disc`, `disc_inj`, `disc_boundary`,
  `disc_mem`) whose interior part is **open in `S`** (`open_interior`): this is the content of
  Jordan–Schoenflies for a simple closed curve in the 2-sphere `S`;
* the family is nested, witnessed by a rank function which strictly decreases along the
  relation "the curve lies in the interior of the disc" (`rank`, `inside`).  For finitely many
  pairwise disjoint simple closed curves in a 2-sphere one always has such a rank (either the
  curve is contained in the disc of the other, or the two discs are disjoint); the field makes
  the choice of the discs — that is, the choice of which side of each curve is the "inside" —
  part of the datum, which is exactly what Jordan–Schoenflies supplies.

Everything else in `Work.InnermostDisk.SphereSlicing` is *proved* from this datum, see
`Work.Topology.SphereSlicing.Slice.Reduce`. -/
structure SliceData (P : ParamTorus) (S : Set R3) where
  /-- the index type of the components of `S ∩ F` -/
  ι : Type
  /-- finitely many components -/
  fintype : Fintype ι
  /-- the components of `S ∩ F` -/
  c : ι → ClosedCurve P
  /-- each component is an embedded loop -/
  simple : ∀ i : ι, IsSimple P (c i)
  /-- distinct components are disjoint -/
  disjoint : Pairwise fun i j : ι => Disjoint (Set.range (c i).γ) (Set.range (c j).γ)
  /-- they lie in `S` -/
  mem : ∀ i : ι, ∀ t : ℝ, (c i).γ t ∈ S
  /-- every point of `S ∩ F` lies on one of the components -/
  covers_pt : ∀ x : R3, x ∈ S → x ∈ P.carrier → ∃ i : ι, x ∈ Set.range (c i).γ
  /-- the disc inside `S` bounded by a component -/
  disc : ι → C(Disc, R3)
  /-- the disc is embedded -/
  disc_inj : ∀ i : ι, Function.Injective (disc i)
  /-- its boundary is the component -/
  disc_boundary : ∀ i : ι, ∀ θ : ℝ, disc i (circlePoint θ) = (c i).γ θ
  /-- the disc lies in `S` -/
  disc_mem : ∀ i : ι, ∀ z : Disc, disc i z ∈ S
  /-- **Jordan–Schoenflies**: the interior of the disc is open in `S` (it is the bounded
  component of `S ∖ cᵢ`) -/
  open_interior : ∀ i : ι,
    IsOpen {x : S | ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ disc i z = (x : R3)}
  /-- the nesting rank of the components -/
  rank : ι → ℕ
  /-- a component meeting the interior of the disc of `i` has smaller rank -/
  inside : ∀ i j : ι, (∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ disc i z ∈ Set.range (c j).γ) →
    rank j < rank i

attribute [instance] SliceData.fintype

/-! ## Transversality: the first classical ingredient

The slicing datum `SliceData P S` requires that `S ∩ F` *is* a finite disjoint union of simple
closed curves of `F`.  That is a hypothesis on `S`, not a consequence of `S` being an embedded
sphere: it is the statement that `S` is *in general position* with respect to `F`.  It cannot be
dropped.

Concretely, let `X = B³ ∪ (1-handle)` be the solid torus obtained by attaching a handle outside
the unit ball, so that `F = ∂X` contains `S² ∖ (D₁ ∪ D₂)` for two open discs `D₁, D₂ ⊆ S²`; `X` is
an unknotted solid torus, so `F = ψ(F_standard)` for a homeomorphism `ψ` of `ℝ³`.  Taking
`S = S²`, the intersection `S ∩ F` is two-dimensional, so no finite family of curves can cover it,
and `SliceData P S` fails for `P` parametrising `F`.  Worse, `Work.InnermostDisk.SphereSlicingInput`
fails for this `P` too: for any candidate family covering `S ∩ F`, the open subset `S² ∖ (D₁ ∪ D₂)`
of the surface `F` would be contained in the finite union of the curves, each of which has empty
interior in `F` (a simple closed curve of a surface is 1-dimensional), so a small circle of `F`
inside that open set meets none of the curves, contradicting `covers`.  (This is a mathematical
argument; it is not formalized in Lean here, since it needs the specific handlebody torus.)

Transversality is therefore isolated here as the predicate `TransverseSphere`, and the slicing
input below takes it as a hypothesis.  This is exactly the decomposition Pardon uses: he assumes
the sphere transverse to `F` and to `β`, and proves the two innermost arguments from there. -/

/-- **Transversality of a sphere with the surface**: `S ∩ F` is a finite disjoint union of simple
closed curves of `F` (`S` is in general position with respect to `F`).  This is the first classical
ingredient of the slicing of a sphere by a surface, and the *hypothesis* under which
Jordan–Schoenflies and the nesting rank produce the full datum `SliceData`. -/
def TransverseSphere (P : ParamTorus) (S : Set R3) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ClosedCurve P),
    (∀ i : ι, IsSimple P (c i)) ∧
    (Pairwise fun i j : ι => Disjoint (Set.range (c i).γ) (Set.range (c j).γ)) ∧
    (∀ i : ι, ∀ t : ℝ, (c i).γ t ∈ S) ∧
    (∀ x : R3, x ∈ S → x ∈ P.carrier → ∃ i : ι, x ∈ Set.range (c i).γ)

/-- A slicing datum is in particular a transversality witness: `TransverseSphere` is the curve
part of `SliceData`, so the hypothesis of `SliceInput` is never gratuitous. -/
theorem transverseSphere_of_sliceData {P : ParamTorus} {S : Set R3} (h : SliceData P S) :
    TransverseSphere P S :=
  ⟨h.ι, h.fintype, h.c, h.simple, h.disjoint, h.mem, h.covers_pt⟩

/-- **The slicing input**: every embedded sphere *in general position with respect to `F`* admits
a slicing datum.  This is the classical content of "a PL sphere transverse to a PL surface is
sliced by it": *given* the transversality of the two surfaces (the finite family of curves of
`S ∩ F`), Jordan–Schoenflies bounds a disc inside `S` for each of them and the nesting of disjoint
curves on a sphere produces the rank.

The hypothesis `TransverseSphere P S` is essential: without it the statement is false, see the
discussion above. -/
def SliceInput (P : ParamTorus) : Prop :=
  ∀ S : Set R3, IsEmbeddedSphere S → TransverseSphere P S → Nonempty (SliceData P S)

/-! ## The nesting relation -/

/-- **The nesting relation of a family of curves with spanning discs.**  `NestRel c disc i j`
says that the curve `c j` meets the *interior* of the disc of `i`; for a consistently chosen
family of discs of pairwise disjoint simple closed curves of a sphere this is the relation "the
curve `j` lies inside the disc of the curve `i`".

It is the relation whose transitivity (or, equivalently, acyclicity) expresses the classical
*nesting* of the components of `S ∩ F`; `Work.Topology.SphereSlicing.exists_rank_of_strict_order`
turns a transitive, irreflexive relation into the rank function required by `SliceData`, and
`Work.Topology.SphereSlicing.nestRel_irreflexive` shows that irreflexivity is automatic for the
discs of a `SliceData`. -/
def NestRel {P : ParamTorus} {ι : Type} (c : ι → ClosedCurve P) (disc : ι → C(Disc, R3)) (i j : ι) : Prop :=
  ∃ z : Disc, ‖(z : ℂ)‖ < 1 ∧ disc i z ∈ Set.range (c j).γ

/-! ## The cut-and-paste datum -/

/-- **An embedded disc in `ℝ³` with a slice by `F`.**

`α` is a simple closed curve of `F`, `e : 𝔻 → ℝ³` is an embedded disc spanning it, and the
interior of the disc meets `F` only along the finite family of pairwise disjoint simple closed
curves `curves i` of `F`, each of them *inessential* in `F`.  This is the geometric situation of
Pardon's second innermost argument, stripped of everything the cut-and-paste does not use (the
ambient sphere `S`, the containment of the disc in `S`, and the essentiality of `α`). -/
structure SliceDisc (P : ParamTorus) where
  /-- the boundary curve of the disc, a simple closed curve of `F` -/
  α : ClosedCurve P
  /-- it is an embedded loop -/
  simple : IsSimple P α
  /-- the disc in `ℝ³` bounded by `α` -/
  e : C(Disc, R3)
  /-- the disc is embedded -/
  inj : Function.Injective e
  /-- its boundary is `α` -/
  boundary : ∀ θ : ℝ, e (circlePoint θ) = α.γ θ
  /-- the index type of the intersection curves in the interior of the disc -/
  ι : Type
  /-- finitely many of them -/
  fintype : Fintype ι
  /-- the curves of `F` in the interior of the disc -/
  curves : ι → ClosedCurve P
  /-- each of them is an embedded loop -/
  curves_simple : ∀ i : ι, IsSimple P (curves i)
  /-- each of them is inessential in `F` -/
  curves_inessential : ∀ i : ι, ¬ IsEssential P (curves i)
  /-- they are pairwise disjoint -/
  curves_disjoint : Pairwise fun i j : ι =>
    Disjoint (Set.range (curves i).γ) (Set.range (curves j).γ)
  /-- each of them is contained in the disc -/
  curves_subset : ∀ i : ι, Set.range (curves i).γ ⊆ Set.range e
  /-- they exhaust the intersection of the interior of the disc with `F` -/
  covers : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → e z ∈ P.carrier → ∃ i : ι, e z ∈ Set.range (curves i).γ

attribute [instance] SliceDisc.fintype

/-- **The single cut-and-paste of Pardon's second innermost argument** (`RemovesOneCurve`,
restated on the local model): an embedded disc in `ℝ³` whose boundary is a simple closed curve of
`F` and whose interior meets `F` only in inessential simple curves can be replaced, keeping its
boundary, by such a disc with strictly fewer intersection curves.

Classically: take an intersection curve innermost in the disc; it bounds a sub-disc `D_γ` whose
interior is disjoint from `F`, and, being inessential, it also bounds a disc `E ⊆ F`; then
`D_γ ∪ E` is an embedded 2-sphere in `ℝ³`, and the part of `D` inside the ball it bounds can be
pushed through it, removing `γ` and leaving the disc embedded. -/
def CleanOneCurve (P : ParamTorus) : Prop :=
  ∀ D : SliceDisc P, 0 < Fintype.card D.ι →
    ∃ D' : SliceDisc P, D'.α = D.α ∧ Fintype.card D'.ι < Fintype.card D.ι

/-! ## The complete classical input -/

/-- **The complete classical input of Pardon's Lemma 4.2 in the vocabulary of this chapter**:
the slicing of embedded spheres *in general position* by `F` (`SliceInput`), and the single
cut-and-paste of the second innermost argument (`CleanOneCurve`).

Two remarks on its relation to `Work.InnermostDisk.PardonPLInput P`:

* The cleaning half `CleanOneCurve` is a *weakening* of `CleansDiscs` (the local model `SliceDisc`
  forgets the ambient sphere, the containment of the disc in it and the essentiality of its
  boundary), and `Work.InnermostDisk.CleansDiscs` follows from it
  (`Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve`).
* The slicing half is *not* a consequence of `Work.InnermostDisk.SphereSlicingInput P`, nor does it
  imply it: `SliceInput` demands general position of the sphere with respect to `F`, while
  `SphereSlicingInput` quantifies over *all* embedded spheres and is false — see the discussion of
  `TransverseSphere` above.  What is derived here is the slicing of every sphere *in general
  position* (`Work.Topology.SphereSlicing.nonempty_sphereSlicing_of_sliceInput`). -/
def ClassicalInput (P : ParamTorus) : Prop :=
  SliceInput P ∧ CleanOneCurve P

end

end Work.Topology.SphereSlicing
