import Submission.Work.CoreTopology.Disk

/-!
# The innermost-disc vocabulary

This file sets up the objects in which Pardon's two innermost-disc arguments
(Lemma 4.2, "mustbeinessential", of *On the distortion of knots on embedded surfaces*)
are phrased.  The two arguments are:

* **innermost in the sphere.**  `S` is a (PL) sphere transverse to `F` and to `β`; the
  components of `S ∩ F` are simple closed curves of `F`.  If one of them is essential,
  one of them, `α`, is innermost in `S`: it bounds a disc `D ⊆ S` whose interior meets `F`
  only in curves that are inessential in `F`.  This is the datum recorded by
  `InnermostDisc`; its existence is Pardon's first step, stated as the hypothesis
  `InnermostDiscInput`.

* **innermost in the surface.**  Cutting and pasting `D` along the discs that `F` provides
  for those inessential curves, `D` can be replaced (keeping its boundary `α` fixed and
  keeping it embedded) by a disc whose interior is disjoint from `F`.  This is Pardon's
  second step, stated as the hypothesis `CleansDiscs`, and it is what turns the innermost
  essential curve of `S ∩ F` into a *compressing* loop, i.e. an element of Pardon's set `U`.

The main definitions are

* `Disc` — the closed unit disc `𝔻 ⊆ ℂ`, the model of the 2-disc;
* `IsSpanningDisc P α e` — `e` is an embedding of `𝔻` in `ℝ³` whose boundary is `α`
  (the disc is not required to avoid `F`; `IsBoundingDisk` is the case where it does);
* `BoundsDiscInSurface P α` — Pardon's notion of *inessential*: `α` bounds a disc in `F`;
* `InnermostDisc P S` — the pair (innermost essential curve of `S ∩ F`, the disc it bounds
  in `S`), together with the finite family of inessential curves of `F` in the interior of
  that disc;
* `InnermostDiscInput P S` — Pardon's first step: if `S` contains an essential loop of `F`,
  there is an innermost disc inside `S`;
* `CleansDiscs P` — Pardon's second step: an innermost disc can be cleaned up so that its
  interior is disjoint from `F`;
* `CleansInSphere P S` — the resulting statement, which is exactly what the reduction of
  `Work.CoreTopology.mustbeinessential` needs.

Everything downstream (in particular `Work.InnermostDisk.Reduction`) turns these into
Pardon's lemma.  The two inputs `InnermostDiscInput` and `CleansDiscs` are classical
topological facts — Jordan–Schoenflies in the sphere, PL transversality and the
cut-and-paste of an embedded disc in `ℝ³` — which are *not* available in Mathlib; they are
therefore kept as explicit hypotheses.  See `Submission/Work/InnermostDisk/README.md`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section

/-- The standard closed unit disc `𝔻 = {z : ℂ | ‖z‖ ≤ 1}`, the model of the 2-disc. -/
abbrev Disc : Type := Metric.closedBall (0 : ℂ) 1

/-! ## Discs in `ℝ³` spanning a curve of the surface -/

/-- `e` presents the closed curve `α` of the surface `F = P.carrier` as the boundary of an
embedded disc in `ℝ³`: `e` is injective on `𝔻` and its boundary circle maps to `α`.

No condition is imposed on the interior of the disc; in particular the interior may meet `F`
(that is the situation in Pardon's innermost argument).  Adding the requirement that the
interior avoids `F` gives `IsBoundingDisk`, i.e. Pardon's set `U`. -/
def IsSpanningDisc (P : ParamTorus) (α : ClosedCurve P) (e : C(Disc, R3)) : Prop :=
  Function.Injective e ∧ ∀ θ : ℝ, e (circlePoint θ) = α.γ θ

/-- `IsBoundingDisk` is exactly `IsSpanningDisc` together with the requirement that the
interior of the disc be disjoint from `F`. -/
theorem isBoundingDisk_iff (P : ParamTorus) (α : ClosedCurve P) (e : C(Disc, R3)) :
    IsBoundingDisk P α e ↔
      IsSpanningDisc P α e ∧ ∀ z : Disc, ‖(z : ℂ)‖ < 1 → e z ∉ P.carrier := by
  simp only [IsBoundingDisk, IsSpanningDisc, and_assoc]

/-- The range of a spanning disc contains `α`. -/
theorem IsSpanningDisc.range_subset (P : ParamTorus) (α : ClosedCurve P) (e : C(Disc, R3))
    (h : IsSpanningDisc P α e) : Set.range α.γ ⊆ Set.range e :=
  fun x ⟨t, ht⟩ => ⟨circlePoint t, by rw [h.2 t, ht]⟩

/-! ## Pardon's notion of inessentiality -/

/-- Pardon's notion of **inessential**: the closed curve `α` of `F` bounds a disc *in the
surface* `F`.  This is the notion used in the statement of Pardon's Lemma
("every curve in `S ∩ F` is inessential in `F`"); it agrees with `¬ IsEssential P α`
(the vanishing of the winding vector), see
`Work.InnermostDisk.boundsDiscInSurface_iff_not_isEssential`. -/
def BoundsDiscInSurface (P : ParamTorus) (α : ClosedCurve P) : Prop :=
  ∃ e : C(Disc, P.carrier), ∀ θ : ℝ, (e (circlePoint θ) : R3) = α.γ θ

/-! ## Embedded spheres -/

/-- A subset of `ℝ³` which is the image of an injective continuous map of the unit sphere:
a topologically embedded 2-sphere.  (Pardon works with PL spheres; this predicate only
records the topological shape, which is what the hypotheses of the two innermost steps are
about.) -/
def IsEmbeddedSphere (S : Set R3) : Prop :=
  ∃ e : C(Metric.sphere (0 : R3) 1, R3), Function.Injective e ∧ Set.range e = S

/-! ## The innermost disc produced by the first step -/

/-- **The datum of Pardon's first innermost argument.**

An essential simple closed curve `α` of `F` lying in `S` together with an embedded disc
`e ⊆ S` bounded by it, subject to the key property of an *innermost* curve: the interior of
the disc meets `F` only along a finite family of pairwise disjoint simple closed curves of
`F`, each of them inessential in `F`.

This is exactly the output of "choose an essential component of `S ∩ F` innermost in `S`"
when `S` is a PL sphere transverse to `F`:
the components of `S ∩ F` are the curves `curves i`, `covers` says that the interior of the
disc contains no other intersection with `F`, and innermostness in `S` says that none of the
curves is essential. -/
structure InnermostDisc (P : ParamTorus) (S : Set R3) where
  /-- The innermost essential curve of `S ∩ F`. -/
  α : ClosedCurve P
  /-- It is an embedded loop. -/
  simple : IsSimple P α
  /-- It is essential in `F`. -/
  essential : IsEssential P α
  /-- It lies in `S`. -/
  mem : ∀ t : ℝ, α.γ t ∈ S
  /-- The disc in `ℝ³` bounded by `α`. -/
  e : C(Disc, R3)
  /-- The disc is embedded. -/
  inj : Function.Injective e
  /-- Its boundary is `α`. -/
  boundary : ∀ θ : ℝ, e (circlePoint θ) = α.γ θ
  /-- The disc lies inside `S`. -/
  e_mem : ∀ z : Disc, e z ∈ S
  /-- The index type of the family of inessential curves in the interior of the disc. -/
  ι : Type
  /-- The family is finite (so that an innermost one can be chosen). -/
  fintype : Fintype ι
  /-- The family of curves of `F` in the interior of the disc. -/
  curves : ι → ClosedCurve P
  /-- Each of them is an embedded loop. -/
  curves_simple : ∀ i : ι, IsSimple P (curves i)
  /-- Each of them is inessential in `F`. -/
  curves_inessential : ∀ i : ι, ¬ IsEssential P (curves i)
  /-- They are pairwise disjoint. -/
  curves_disjoint : Pairwise fun i j => Disjoint (Set.range (curves i).γ) (Set.range (curves j).γ)
  /-- Each of them is contained in the disc. -/
  curves_subset : ∀ i : ι, Set.range (curves i).γ ⊆ Set.range e
  /-- They exhaust the intersection of the interior of the disc with `F`. -/
  covers : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → e z ∈ P.carrier → ∃ i : ι, e z ∈ Set.range (curves i).γ

attribute [instance] InnermostDisc.fintype

namespace InnermostDisc

variable {P : ParamTorus} {S : Set R3}

/-- The curve of an innermost disc is a spanning disc of itself (redundant restatement used
to interface with `Work.InnermostDisk.IsSpanningDisc`). -/
theorem isSpanningDisc (D : InnermostDisc P S) : IsSpanningDisc P D.α D.e :=
  ⟨D.inj, D.boundary⟩

end InnermostDisc

/-! ## The two topological inputs -/

/-- **Pardon's first innermost step (innermost in the sphere).**

If a sphere `S` meets `F` along an essential curve, then there is an essential simple closed
curve `α ⊆ S` which is *innermost*: it bounds a disc inside `S` whose interior meets `F` only
in curves inessential in `F` (`InnermostDisc`).

For a PL embedded sphere `S` transverse to `F` this is Pardon's "consider the set of all such
essential curves as a collection of curves on `S`, and let `α` be any such curve that is
innermost": the components of `S ∩ F` are finitely many simple closed curves (transversality
in the PL category), each of them bounds a disc in `S` (Jordan–Schoenflies in the 2-sphere),
and one takes an essential one minimal with respect to containment.  It is stated here for an
arbitrary set `S` because only the sphere of the application is ever used; the sphere-conditioned
form is `SphereInnermostInput`. -/
def InnermostDiscInput (P : ParamTorus) (S : Set R3) : Prop :=
  (∃ α : ClosedCurve P, IsEssential P α ∧ ∀ t : ℝ, α.γ t ∈ S) → Nonempty (InnermostDisc P S)

/-- The same input, conditioned on `S` being an embedded sphere. -/
def SphereInnermostInput (P : ParamTorus) : Prop :=
  ∀ S : Set R3, IsEmbeddedSphere S → InnermostDiscInput P S

/-- The sphere-conditioned input gives the input for any embedded sphere. -/
theorem InnermostDiscInput.of_sphere {P : ParamTorus} {S : Set R3}
    (h : SphereInnermostInput P) (hS : IsEmbeddedSphere S) : InnermostDiscInput P S :=
  h S hS

/-- **Pardon's second innermost step (innermost in the surface).**

An innermost disc (whose interior meets `F` only in inessential curves of `F`) can be cleaned
up: keeping its boundary `α` fixed and remaining embedded, the disc can be modified so that its
interior is disjoint from `F`.  Equivalently, the innermost curve is a *compressing* loop, i.e.
an element of Pardon's set `U`.

This is Pardon's "considering such an inessential curve which is innermost in `F`, it is easy
to see that we can modify `D` so as to eliminate this intersection, while keeping `D`
embedded.  Proceeding in this way, we may eliminate all the intersections of `D` with `F`".
The proof is a cut-and-paste in `ℝ³`: an intersection curve `γ` innermost in `D` bounds a disc
`D_γ ⊆ D` with interior disjoint from `F`, and, being inessential, it also bounds a disc `E ⊆ F`;
`D_γ ∪ E` is an embedded 2-sphere in `ℝ³`, and the part of `D` inside the ball it bounds can be
pushed through it to the other side of `F`. -/
def CleansDiscs (P : ParamTorus) : Prop :=
  ∀ (S : Set R3) (D : InnermostDisc P S), BoundsDiskInComplement P D.α

/-! ## The form in which the reduction consumes the inputs -/

/-- `CleansInSphere P S`: every essential loop of `F` contained in `S` can be replaced by a
simple essential loop contained in `S` which bounds a disc whose interior is disjoint from `F`.

This is the (slightly weakened) form of `hclean` in
`Work.CoreTopology.mustbeinessential`: there the replacement loop is additionally required to
meet `β` no more often than the given loop, which is *not* what Pardon's argument produces
(his replacement loop is the innermost component of `S ∩ F`, and its intersection with `β` is
bounded by `#(S ∩ β)`, not by `#(α ∩ β)`).  For the proof of Pardon's lemma the present form
is enough, see `Work.InnermostDisk.Reduction.mustbeinessential_of_cleansInSphere`. -/
def CleansInSphere (P : ParamTorus) (S : Set R3) : Prop :=
  ∀ α : ClosedCurve P, IsEssential P α → (∀ t : ℝ, α.γ t ∈ S) →
    ∃ α' : ClosedCurve P, IsSimple P α' ∧ IsEssential P α' ∧
      BoundsDiskInComplement P α' ∧ ∀ t : ℝ, α'.γ t ∈ S

/-! ## A constant closed curve -/

/-- The constant closed curve of `F` at a point of `F`. -/
def constCurve (P : ParamTorus) (x : R3) (hx : x ∈ P.carrier) : ClosedCurve P where
  γ := fun _ => x
  cont := continuous_const
  periodic := fun _ => rfl
  mem := fun _ => hx

@[simp] theorem constCurve_apply (P : ParamTorus) (x : R3) (hx : x ∈ P.carrier) (t : ℝ) :
    constCurve P x hx t = x := rfl

end

end Work.InnermostDisk
