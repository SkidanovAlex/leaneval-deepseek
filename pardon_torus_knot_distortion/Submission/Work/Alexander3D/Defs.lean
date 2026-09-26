import Submission.Work.Collar3D.CutAndPaste.Defs
import Submission.Work.Collar3D.Isotopy
import Submission.Work.Collar3D.Chart.Ambient

/-!
# `Work.Alexander3D` — Alexander's theorem, the gluing of two discs, and the local push-off

This chapter supplies the 3-dimensional topology that the last remaining input of Pardon's
argument, `Work.Collar3D.PinchedSurgery`, rests on.  Its contents:

* the **gluing lemma** (`Work.Alexander3D.gluesToSphere_isEmbeddedSphereSet`): two embedded discs
  with a common boundary curve and disjoint interiors form an embedded `2`-sphere;
* **Alexander's theorem** for a locally flat embedded `2`-sphere in `ℝ³` (`AlexanderBallTheorem`),
  with the proved partial results (`roundSphere_boundsBall`) and the point-set consequences of
  `Work.Collar3D` (`separates_of_boundsBall`);
* the **isotopy extension theorem** (`IsotopyExtension3D`, identified with the named input
  `Work.Collar3D.IsotopyExtension`), with the chart-supported case *proved* in
  `Work.Collar3D.ambientIsotopyOfChart`;
* the **regular-neighbourhood theorem along an inessential simple closed curve** of a locally flat
  surface (`InessentialCurveCollar`);
* the **local push-off** (`LocalPushOff`): the collar-local form of Pardon's cut-and-paste step,
  *proved* in the compactly-contained case
  (`Work.Alexander3D.exists_pushOff_of_collar`, module `CollarShift`).

## Conventions

`R3 = EuclideanSpace ℝ (Fin 3)`, `Disc = 𝔻 = Metric.closedBall (0 : ℂ) 1`,
`Sphere2 = Metric.sphere (0 : R3) 1` (the round unit `2`-sphere), `Ball3 = Metric.closedBall
(0 : R3) 1` (the round closed unit ball), and `circlePoint` is the standard parametrisation
`θ ↦ e^{iθ}` of the boundary of the disc (`Work.Smooth.Jordan.circlePoint`), matching the
convention of `Work.Collar3D.PinchedSurgery`.
-/

open Set

namespace Work.Alexander3D

/-- The ambient Euclidean space `ℝ³`. -/
abbrev R3 : Type := Work.Collar3D.R3

/-- The model disc `𝔻 = {z : ℂ | ‖z‖ ≤ 1}`. -/
abbrev Disc : Type := Work.Collar3D.Disc

/-- The model circle `S¹`. -/
abbrev Circle : Type := Work.Collar3D.Circle

/-- The standard parametrisation `θ ↦ e^{iθ}` of the boundary of the model disc, in the
convention of `Work.Collar3D.PinchedSurgery`. -/
noncomputable abbrev circlePoint (θ : ℝ) : Disc := Work.Smooth.Jordan.circlePoint θ

/-- The round unit `2`-sphere, as the model of an embedded sphere. -/
abbrev Sphere2 : Type := Metric.sphere (0 : R3) 1

/-- The round closed unit ball. -/
abbrev Ball3 : Set R3 := Metric.closedBall (0 : R3) 1

noncomputable section

/-! ## Embedded spheres and the balls they bound -/

/-- A set which is the image of an injective continuous map of the round unit `2`-sphere: a
topologically embedded `2`-sphere. -/
def IsEmbeddedSphereSet (S : Set R3) : Prop :=
  ∃ f : C(Sphere2, R3), Function.Injective f ∧ Set.range f = S

/-- A **locally flat embedded `2`-sphere**: an embedded sphere which is tame at every one of its
points (the hypothesis under which Alexander's theorem is used; for the *wild* sphere the
statement "bounds a ball" is still a theorem of Alexander, but its boundary is not tame and the
isotopy-extension half of the push-through fails). -/
def IsLocallyFlatSphere (S : Set R3) : Prop :=
  IsEmbeddedSphereSet S ∧ Work.Smooth.PushThrough3D.LocallyFlatSet S

/-- `K` is a closed ball with boundary `S`: a compact region whose frontier is `S` and which is
homeomorphic to the round closed unit ball. -/
structure BoundsBall (K S : Set R3) : Prop where
  /-- the region is compact -/
  isCompact : IsCompact K
  /-- its frontier is the sphere -/
  frontier_eq : frontier K = S
  /-- it is a (closed) ball -/
  ball_homeo : Nonempty (K ≃ₜ Ball3)

/-- `K` is a **standard** ball: an ambient homeomorphism of `ℝ³` carries it to the round unit
ball.  This is the form in which the push-through consumes the ball bounded by the pinching
sphere: it is exactly what makes the inside of the ball pushable onto its outside. -/
def IsStandardBall (K : Set R3) : Prop := ∃ H : R3 ≃ₜ R3, H '' K = Ball3

/-- **Alexander's theorem** for a locally flat embedded `2`-sphere in `ℝ³`: it bounds a standard
ball.  (Alexander's theorem for a *wild* sphere gives a ball homeomorphic to the standard one, but
not standardly embedded — the famous failure of the `3`-dimensional Schoenflies theorem; the
local-flatness — tameness — hypothesis is what makes the standard position available, and it is
satisfied by every sphere this development produces.) -/
def AlexanderBallTheorem : Prop :=
  ∀ S : Set R3, IsLocallyFlatSphere S → ∃ K : Set R3, BoundsBall K S ∧ IsStandardBall K

/-! ## The gluing of two discs -/

/-- The union of the images of two discs, as a subset of `ℝ³`. -/
def TwoDiscSphere (β σ : C(Disc, R3)) : Set R3 := Set.range (fun z : Disc => β z) ∪
  Set.range (fun z : Disc => σ z)

/-- The two discs have the same boundary curve. -/
def SameBoundary (β σ : C(Disc, R3)) : Prop :=
  ∀ θ : ℝ, β (circlePoint θ) = σ (circlePoint θ)

/-- **The hypothesis of the gluing lemma**: two embedded discs whose interiors are disjoint and
whose boundaries agree.  Then their union is an embedded `2`-sphere. -/
def GluesToSphere (β σ : C(Disc, R3)) : Prop :=
  Function.Injective β ∧ Function.Injective σ ∧ SameBoundary β σ ∧
  Disjoint (β '' {z : Disc | ‖((z : Disc) : ℂ)‖ < 1})
    (σ '' {z : Disc | ‖((z : Disc) : ℂ)‖ < 1})

/-- **The transversality hypothesis of the local-flatness half of the gluing lemma**: at every
point of the common boundary curve there is a chart of `ℝ³` carrying the two disc images to two
half-planes meeting along their common edge — that is, the two discs meet *transversally* along
the curve. -/
def TransverseAlongBoundary (β σ : C(Disc, R3)) : Prop :=
  ∀ θ : ℝ, ∃ (U : Set R3) (_ : IsOpen U) (hx : β (circlePoint θ) ∈ U)
      (Φ : U ≃ₜ Metric.ball (0 : R3) 1),
    Φ ⟨β (circlePoint θ), hx⟩ = 0 ∧
    (∀ y : R3, y ∈ Metric.ball (0 : R3) 1 →
      ((∃ u : U, (u : R3) ∈ Set.range (fun z : Disc => β z) ∧ (Φ u : R3) = y) ↔
        y 0 = 0 ∧ 0 ≤ y 2)) ∧
    (∀ y : R3, y ∈ Metric.ball (0 : R3) 1 →
      ((∃ u : U, (u : R3) ∈ Set.range (fun z : Disc => σ z) ∧ (Φ u : R3) = y) ↔
        y 2 = 0 ∧ 0 ≤ y 0))

/-! ## Isotopy extension -/

/-- **The isotopy extension theorem** for a compactly supported isotopy of a locally flat closed
set, with support in a prescribed open set.  This is the Edwards–Kirby theorem, and it is
literally the named input `Work.Collar3D.IsotopyExtension` of the collar chapter (stated there in
exactly this form); the chart-supported case is *proved*
(`Work.Collar3D.ambientIsotopyOfChart`). -/
def IsotopyExtension3D : Prop :=
  ∀ (A : Set R3), IsClosed A → (∀ x ∈ A, Work.Smooth.PushThrough3D.LocallyFlatSetAt A x) →
    ∀ (φ : ℝ → A ≃ₜ A) (_ : Continuous fun p : ℝ × A => φ p.1 p.2)
      (_ : Continuous fun p : ℝ × A => (φ p.1).symm p.2) (K : Set A) (hK : IsCompact K)
      (_ : ∀ (t : ℝ) (x : A), x ∉ K → φ t x = x)
      (V : Set R3) (hV : IsOpen V) (hKsub : (Subtype.val '' K) ⊆ V),
      ∃ H : Work.Collar3D.AmbientIsotopy, H.supportedIn V ∧
        ∀ (t : ℝ) (x : A), H t (x : R3) = (φ t x : R3)

/-! ## The regular-neighbourhood theorem along an inessential curve -/

/-- **The regular-neighbourhood (bicollar) theorem along an inessential simple closed curve of a
locally flat surface.**  Let `F ⊆ ℝ³` be locally flat, let `γ` be a simple closed curve in `F`
(in the workspace convention: continuous, `2π`-periodic, injective on one period), and suppose
`γ` is *inessential* in `F`: it is the boundary of a disc `Σ` whose image lies in `F`.  Then `F`
has a collar along `γ`.

The classical content is the regular-neighbourhood theorem;
`Work.Collar3D.RegularNeighbourhoodCurve` is the same theorem with the *framing*
(`HasAnnularNeighbourhood F γ`) in place of the inessentiality, and
`Work.Collar3D.hasCollar_planeCircle` certifies the non-vacuity of both.  The inessentiality
hypothesis here is the one supplied by Pardon's argument (the intersection curve bounds a disc of
the surface), and it is what supplies the framing. -/
def InessentialCurveCollar : Prop :=
  ∀ (F : Set R3) (γ : ℝ → R3),
    Work.Smooth.PushThrough3D.LocallyFlatSet F →
    Work.Collar3D.IsCircleCurve γ →
    (∀ θ : ℝ, γ θ ∈ F) →
    (∃ Sig : C(Disc, R3), (∀ θ : ℝ, Sig (circlePoint θ) = γ θ) ∧ ∀ z : Disc, Sig z ∈ F) →
    Work.Collar3D.HasCollar F γ

/-! ## The local push-off -/

/-- **Pardon's cut-and-paste step, in collar-local form** — the single classical proposition this
chapter reduces `Work.Collar3D.PinchedSurgery` to.

Let `F ⊆ ℝ³` be a locally flat surface with a collar `c` along a simple closed curve `γ`, let
`e : 𝔻 → ℝ³` be an embedded disc and `β : 𝔻 → ℝ³` an embedded sub-disc of it whose boundary curve
is `γ` and whose interior misses `F`, and let `C` be a compact set disjoint from the closed
sub-disc `β(𝔻)`.  Assume the local form of the innermost clause: every point of `F ∩ c.U` which
lies in the interior of `e` already lies on `γ`.

Then there is a homeomorphism `H` of `ℝ³`, the identity outside the collar, which pushes the disc
`e` off `F` inside the collar except into `C` — `H (e z) ∈ F` for an interior point `z` with
`e z ∈ c.U` only if `H (e z) ∈ C` — fixes `C` pointwise, and fixes the boundary curve of `e`
pointwise.

This is the local content of Pardon's surgery: the disc crosses the surface along `γ`, and the
crossing is pushed through by an isotopy supported in a collar of `γ`.  It is *proved* in the
compactly contained case by `Work.Alexander3D.exists_pushOff_of_collar` (with the sharper
conclusion `H (e z) ∉ F`); the general case (the disc's part in the collar not compactly contained
in the model, or its boundary curve touching `γ`) is the residual classical input and is discussed
in the README. -/
def LocalPushOff : Prop :=
  ∀ (F : Set R3), Work.Smooth.PushThrough3D.LocallyFlatSet F →
  ∀ (γ : ℝ → R3) (c : Work.Collar3D.Collar F γ) (e β : C(Disc, R3)) (C : Set R3),
    Function.Injective e →
    Function.Injective β →
    Set.range (fun z : Disc => β z) ⊆ Set.range (fun z : Disc => e z) →
    (∀ θ : ℝ, β (circlePoint θ) = γ θ) →
    (∀ z : Disc, ‖((z : Disc) : ℂ)‖ < 1 → β z ∉ F) →
    IsCompact C →
    Disjoint C (Set.range (fun z : Disc => β z)) →
    (∀ x : R3, x ∈ c.U → x ∈ F → (∃ z : Disc, ‖((z : Disc) : ℂ)‖ < 1 ∧ e z = x) →
      x ∈ Set.range γ ∨ x ∈ C) →
    ∃ H : R3 ≃ₜ R3,
      (∀ x : R3, x ∉ c.U → H x = x) ∧
      (∀ x : R3, x ∈ C → H x = x) ∧
      (∀ z : Disc, ‖((z : Disc) : ℂ)‖ < 1 → e z ∈ c.U → H (e z) ∈ F → H (e z) ∈ C) ∧
      (∀ θ : ℝ, H (e (circlePoint θ)) = e (circlePoint θ))

end

end Work.Alexander3D
