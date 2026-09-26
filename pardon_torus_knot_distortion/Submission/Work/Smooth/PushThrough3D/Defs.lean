import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Topology.SphereSlicing.Defs

/-!
# `Work.Smooth.PushThrough3D` — the three-dimensional cut-and-paste inputs

This chapter carries the **3-dimensional** half of Pardon's second innermost argument, i.e. the
inputs which the delivered chapter `Submission/Work/Smooth/SphereJordan` isolates in
`Submission/Work/Smooth/SphereJordan/Pasting.lean` and consumes in its `FinalField.lean`:

* `Work.Smooth.SphereJordan.SurfaceDiscPushOff Work.CoreTopology.standard` — the push-off of a
  surface disc (the "cap");
* `Work.Smooth.SphereJordan.PinchedPushThrough Work.CoreTopology.standard` — Pardon's surgery in
  the *pinched* configuration (Alexander's theorem + isotopy extension).

The two statements are reduced here to **one named classical input each**, stated below in the
working form in which the classical facts (Alexander's sphere theorem, isotopy extension, and the
tameness of the embedded surfaces) are visible; the derivations are in the modules `PushOff` and
`Pinched`.

## The vocabulary

* `LocallyFlatSetAt F x`, `LocallyFlatSet F` — the local flatness (tameness) of a *set*
  `F ⊆ ℝ³` at a point: the ambient-space analogue of the chapter
  `Work.Smooth.SphereJordan`'s `LocallyFlatAlong` for a disc;
* `IsFlatAt e x`, `IsFlatDisc e` — the concrete sufficient condition for the local flatness of an
  embedded disc that the flat discs of Pardon's application satisfy: the disc lies in a plane and
  its image contains a *planar* neighbourhood of each of its interior points (e.g. a flat disc, or
  a flat disc cut out of a plane by a box, transported by an ambient homeomorphism);
* `SurfacePushOffInput` — the push-off of a surface disc, in the abstract form;
* `PinchedSurgeryInput` — Pardon's pinched surgery, in the abstract form (an ambient
  homeomorphism pushing one side of an embedded disc through a locally flat surface, fixing the
  boundary curve and the curves that must survive).

Nothing outside `Submission/Work/Smooth/PushThrough3D/` is modified.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.PushThrough3D

noncomputable section

/-- The standard torus of revolution — the surface for which the 3-dimensional inputs are
needed (`Work.Smooth.SphereJordan.cleansDiscsAll_field_of_plane` consumes exactly
`SurfaceDiscPushOff Work.CoreTopology.standard` and `CurvesInterior Work.CoreTopology.standard`,
or `PinchedPushThrough Work.CoreTopology.standard`). -/
abbrev standardTorus : Work.CoreTopology.ParamTorus := Work.CoreTopology.standard

/-- The model disc `𝔻` of the sibling chapters. -/
abbrev Disc3 : Type := Work.Smooth.Jordan.Disc

/-- The boundary circle `θ ↦ e^{iθ}` of the model disc. -/
abbrev circlePoint3 : ℝ → Disc3 := Work.Smooth.Jordan.circlePoint

/-- The two boundary parametrisations of the model disc in the workspace agree
(`Work.CoreTopology.circlePoint` and `Work.Smooth.Jordan.circlePoint` are the same map). -/
theorem coreCirclePoint_eq (θ : ℝ) :
    Work.CoreTopology.circlePoint θ = Work.Smooth.Jordan.circlePoint θ := Subtype.ext rfl

/-! ## Local flatness of a subset of `ℝ³` -/

/-- **Local flatness of a set `F ⊆ ℝ³` at a point `x ∈ F`.**

At `x` the set `F` looks like a *plane*: some open neighbourhood `U` of `x` is carried by a
homeomorphism `Φ` onto the unit ball of `ℝ³` with `Φ x = 0` and `F ∩ U` mapped onto the equatorial
plane `{y 2 = 0}` of the ball.

This is the ambient-space analogue of `Work.Smooth.SphereJordan.LocallyFlatAlong` (which is the
special case `F = range e` for an embedded disc `e`), and it is the precise form of the
*tameness* which the 3-dimensional cut-and-paste requires of the surfaces it manipulates: an
arbitrary topological embedding of a surface can be wildly embedded along a curve, and then no
collar — hence no push-off — exists.  See §8.4 of the README of
`Submission/Work/Smooth/SphereJordan`. -/
def LocallyFlatSetAt (F : Set R3) (x : R3) : Prop :=
  ∃ (U : Set R3) (_ : IsOpen U) (hx : x ∈ U) (Φ : U ≃ₜ Metric.ball (0 : R3) 1),
    Φ ⟨x, hx⟩ = 0 ∧
    ∀ y : R3, y ∈ Metric.ball (0 : R3) 1 →
      ((∃ u : U, (u : R3) ∈ F ∧ (Φ u : R3) = y) ↔ y 2 = 0)

/-- A set `F ⊆ ℝ³` is **locally flat** (tame) if it is locally flat at each of its points. -/
def LocallyFlatSet (F : Set R3) : Prop := ∀ x ∈ F, LocallyFlatSetAt F x

/-- A **tame disc**: the disc of `Work.Smooth.SphereJordan.LocallyFlat`, under a shorter name. -/
def TameDisc (e : C(Disc3, R3)) : Prop := Work.Smooth.SphereJordan.LocallyFlat e

theorem tameDisc_iff (e : C(Disc3, R3)) : TameDisc e ↔ Work.Smooth.SphereJordan.LocallyFlat e :=
  Iff.rfl

/-! ## The flat discs of Pardon's application -/

/-- **A flat disc**: an embedded disc lying in a plane, whose image contains a *planar*
neighbourhood of each of its interior points.  Equivalently (see `IsFlatDisc.locallyFlat`) the
disc is contained in a plane `{y | (L y) 2 = (L x) 2}` and equals the intersection of that plane
with a neighbourhood of `x`.

This is the shape of the discs that Pardon's argument actually produces: the discs cut out of a
plane by the box `∂PBox s c σ` (a convex polygon in a plane, parametrised by a homeomorphism of
the model disc), and their images under an ambient homeomorphism.  Local flatness of such a disc
is proved by hand in `Work.Smooth.PushThrough3D.Flat`
(`Work.Smooth.PushThrough3D.locallyFlat_of_isFlatDisc`). -/
def IsFlatAt (e : C(Disc3, R3)) (x : R3) : Prop :=
  ∃ (r : ℝ) (L : R3 ≃ₗᵢ[ℝ] R3), 0 < r ∧
    (∀ z : Disc3, (L (e z - x)) 2 = 0) ∧
    ∀ y : R3, (L (y - x)) 2 = 0 → dist y x < r → y ∈ Set.range (fun z : Disc3 => e z)

/-- A disc is **flat** when it is flat at each point of the image of its *interior*. -/
def IsFlatDisc (e : C(Disc3, R3)) : Prop :=
  ∀ x ∈ (fun z : Disc3 => e z) '' {z : Disc3 | ‖(z : ℂ)‖ < 1}, IsFlatAt e x

/-! ## The first input: the push-off of a surface disc -/

/-- **The push-off of a surface disc (the "cap"), in the abstract form.**

Let `F ⊆ ℝ³` be a locally flat surface, let `e : 𝔻 → ℝ³` be a tame embedded disc, and let
`β : 𝔻 → ℝ³` be an embedded disc *contained in the image of `e`*, whose boundary curve
`θ ↦ β (e^{iθ})` is disjoint from `F` and whose interior meets `F` exactly along the curve
`γ : ℝ → ℝ³` (the *innermost clause*), where `γ` is a simple closed curve of `F` which bounds a disc
`Σ` *in the surface* `F`.

Then `β` can be pushed off the surface: there is an embedded disc `cap` with the *same boundary
curve* as `β`, whose interior is disjoint from `F`, and whose interior meets the image of `e` only
along that boundary curve.

Geometrically this is the cap of Pardon's cut-and-paste: `β` is the innermost sub-disc of the slice
disc `e`, its interior crosses `F` along the inessential curve `γ`, and the surface disc `Σ ⊆ F`
bounded by `γ` — pushed to one side of `F` — fills the hole, while the region of `β` outside `γ`
is pushed off the disc `e` along a collar.  The two ingredients of the proof are the local
flatness of `F` along `γ` and of `e`, and the inessentiality of `γ` (the disc `Σ`); the conclusion
is *false* without the inessentiality (see `Work.Smooth.SphereJordan.NaiveSurfaceDiscPushOff` and
`Work.Smooth.SphereJordan.not_naiveSurfaceDiscPushOff_standard`) and without the local flatness
(§8.4 of the sibling README).

**Classical content.**  The existence of the one-sided collars along `γ` is the (topological)
regular-neighbourhood theorem for locally flat surfaces in `ℝ³`, and the push-through uses
Alexander's theorem for the sphere `β ∪ Σ` (an embedded 2-sphere bounds a ball) together with the
extension of the isotopy of `β ∪ Σ` to an ambient isotopy. -/
def SurfacePushOffInput : Prop :=
  ∀ (F : Set R3) (e β : C(Disc3, R3)) (γ : ℝ → R3),
    Function.Injective e →
    Work.Smooth.SphereJordan.LocallyFlat e →
    Function.Injective β →
    Set.range (fun z : Disc3 => β z) ⊆ Set.range (fun z : Disc3 => e z) →
    (∀ θ : ℝ, β (circlePoint3 θ) ∉ F) →
    (∀ z : Disc3, ‖(z : ℂ)‖ < 1 → β z ∈ F → ∃ θ : ℝ, β z = γ θ) →
    (∃ Sig : C(Disc3, R3),
      (∀ θ : ℝ, Sig (circlePoint3 θ) = γ θ) ∧ ∀ z : Disc3, Sig z ∈ F) →
    (∀ x ∈ Set.range γ, LocallyFlatSetAt F x) →
    ∃ cap : C(Disc3, R3), Function.Injective cap ∧
      (∀ θ : ℝ, cap (circlePoint3 θ) = β (circlePoint3 θ)) ∧
      (∀ z : Disc3, ‖(z : ℂ)‖ < 1 → cap z ∉ F) ∧
      (∀ z : Disc3, ‖(z : ℂ)‖ < 1 → cap z ∈ Set.range (fun w : Disc3 => e w) →
        ∃ θ : ℝ, cap z = β (circlePoint3 θ))

/-! ## The second input: the pinched surgery -/

/-- **Pardon's pinched surgery, in the abstract form.**

Let `F ⊆ ℝ³` be a surface, `e : 𝔻 → ℝ³` an embedded disc, `β : 𝔻 → ℝ³` an embedded *sub*-disc of
the image of `e` whose boundary curve `γ` lies in `F`, whose interior is disjoint from `F`, and
which bounds a disc `Σ ⊆ F` (so `γ` is *inessential* in `F`).  Let `C ⊆ ℝ³` be a compact set
disjoint from the closed sub-disc `β(𝔻)` (the curves of the configuration that must survive), and
assume the **innermost clause for `e`**: every interior point of `e` that meets `F` already lies on
the curve `γ` or in `C` — i.e. the only crossings of the interior of `e` with `F` that the surgery
has to remove are the ones along `γ`.

Then there is a homeomorphism `H` of `ℝ³` which

* fixes the boundary curve `θ ↦ e (e^{iθ})` of `e` *pointwise*,
* fixes `C` pointwise,
* pushes the *interior* of the disc `e` off `F` except into `C`: `H (e z) ∈ F` for an interior `z`
  only if `H (e z) ∈ C`.

Both hypotheses on `C` are automatic in Pardon's application:
* `Disjoint C β(𝔻)`: `C` there is the finite union of the *other* intersection curves, which are
  contained in `F` and are disjoint from `β(𝔻)` — from the innermost curve `γ = β(∂𝔻)` by pairwise
  disjointness of the intersection curves and from `β(int 𝔻)` by the innermost clause.  Since
  `β(𝔻)` is compact, this is what allows the isotopy to be supported in a neighbourhood of the
  sub-disc while fixing `C` (the classical argument needs exactly this).
* the innermost clause for `e`: the intersection curves of the slice disc are the `γ` of the
  innermost argument and the surviving curves, which are contained in `C`
  (`Work.Topology.SphereSlicing.SliceDisc.covers`); it is what makes the statement about the removal
  of `γ` only, and not about the (impossible) removal of the remaining intersections.
Both are discharged in `pinchedPushThrough_standard`.  Note that `C = ∅` is permitted; the
statement is then the assertion that the whole interior of `e` can be pushed off `F` while fixing
the boundary curve, under the (then very strong) innermost clause.

Classically `H` is obtained by sliding the sub-disc `β` through the surface `F` along the ball
bounded by the sphere `β ∪ Σ` (Alexander's theorem) and extending the isotopy to the ambient space
(isotopy extension), with the support of the isotopy chosen in a neighbourhood of the sub-disc
`β` which avoids the boundary curve of `e` and the compact set `C`.  This is the (correct,
*global*) form of the step recorded as `PinchedPushThrough`: the purely local modification of a
disc inside a collar of `γ` does not exist (see §8.3 of the sibling README). -/
def PinchedSurgeryInput : Prop :=
  ∀ (F : Set R3) (e β : C(Disc3, R3)) (γ : ℝ → R3) (C : Set R3),
    Function.Injective e →
    Function.Injective β →
    Set.range (fun z : Disc3 => β z) ⊆ Set.range (fun z : Disc3 => e z) →
    (∀ θ : ℝ, β (circlePoint3 θ) = γ θ) →
    (∀ z : Disc3, ‖(z : ℂ)‖ < 1 → β z ∉ F) →
    (∃ Sig : C(Disc3, R3),
      (∀ θ : ℝ, Sig (circlePoint3 θ) = γ θ) ∧ ∀ z : Disc3, Sig z ∈ F) →
    (∀ z : Disc3, ‖(z : ℂ)‖ < 1 → e z ∈ F → e z ∈ C ∨ e z ∈ Set.range γ) →
    IsCompact C →
    Disjoint C (Set.range (fun z : Disc3 => β z)) →
    ∃ H : R3 ≃ₜ R3,
      (∀ θ : ℝ, H (e (circlePoint3 θ)) = e (circlePoint3 θ)) ∧
      (∀ x ∈ C, H x = x) ∧
      (∀ z : Disc3, ‖(z : ℂ)‖ < 1 → H (e z) ∈ F → H (e z) ∈ C)

/-! ## The corrected position hypothesis on the slice discs -/

/-- **The corrected position hypothesis.**  For a slice disc `D`, the intersection curves
produced by the application lie in the *interior* of the disc, i.e. are disjoint from the boundary
curve: `range (D.curves i) ⊆ D.e '' {‖z‖ < 1}`.

This is what `Work.Smooth.SphereJordan.CurvesInterior` is meant to express, and it is the form in
which the position hypothesis of Pardon's application holds (the intersection curves are
components of `F ∩ int D`).  The statement `CurvesInterior` itself — which quantifies over *all*
`SliceDisc` data, and in particular over data in which a "curve" is the boundary curve itself — is
**false**; see `Work.Smooth.PushThrough3D.not_curvesInterior_standard`. -/
def CurvesInInterior {P : Work.CoreTopology.ParamTorus}
    (D : Work.Topology.SphereSlicing.SliceDisc P) : Prop :=
  ∀ i : D.ι, Set.range (D.curves i).γ ⊆
    (fun z : Disc3 => D.e z) '' {z : Disc3 | ‖(z : ℂ)‖ < 1}

end

end Work.Smooth.PushThrough3D
