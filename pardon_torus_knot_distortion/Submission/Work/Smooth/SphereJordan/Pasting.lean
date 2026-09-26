import Submission.Work.Smooth.SphereJordan.RoundSphere

/-!
# The surface side, second step: the cut-and-paste from named classical inputs

The delivered chapter `Submission/Work/Topology/Classical` isolates Pardon's second innermost
argument as the proposition

`Work.Topology.Classical.CutsAlongSubdisc P`

*"given a slice disc `D`, an intersection curve `D.curves j` which is innermost in `D` (it bounds a
sub-disc `f` of `D` whose interior misses the surface and which no other curve meets), produce an
embedded disc with the same boundary as `D`, containing all the other curves, and whose interior
meets the surface only along those other curves."*

This file *reduces* it — and hence `Work.InnermostDisk.CleansDiscs` and the `cleans` field of
`Work.BoxShrink.FinalInput` — to named propositions, and nothing else:

* **`Work.Smooth.SphereJordan.AnnulusSchoenflies`** — the **annulus form of the Schoenflies
  theorem** in the plane: the region between a Jordan curve inside the open unit disc and the
  boundary circle is standard, by a homeomorphism of the disc which fixes the boundary circle
  pointwise *and* carries the curve onto the concentric circle of radius `1/2`, in the prescribed
  parametrisation **up to the orientation sign `s ∈ {1, -1}`** of the embedded disc;
* **`Work.Smooth.SphereJordan.SurfaceDiscPushOff`** — the **push-off of a surface disc** (the
  "cap"): a curve `z₁` of a slice disc `e : 𝔻 → ℝ³` which is a small push-off of a curve `γ` of the
  surface (**inessential in it**: it bounds a disc `E ⊆ F`), off the surface, and whose spanning
  sub-disc contains `γ`, bounds an embedded disc (`cap`) which is disjoint from the surface and
  meets `e(𝔻)` only along `z₁`;
* **`Work.Smooth.SphereJordan.CurvesInterior`** — a **position hypothesis** on the slice discs of
  the torus: the innermost intersection curve is disjoint from the boundary curve of the disc.
  (This is automatic for the transverse slices of Pardon's application; it is what rules out the
  "pinched" configuration, in which the innermost curve touches the boundary curve — a case which
  the constructive route cannot handle and which is covered by the fourth input:)
* **`Work.Smooth.SphereJordan.PinchedPushThrough`** — Pardon's surgery in the *pinched*
  configuration (the innermost curve meets the boundary curve of the disc), which rests on
  Alexander's theorem and isotopy extension and is one case of the classical input
  `Work.Topology.Classical.PushThroughInnermost` of the delivered chapter.

## The construction (the content of `cutsAlongSubdisc_of_props`)

Let `e := D.e`, `γ := D.curves j`, `α := D.α` and `f : 𝔻 → ℝ³` the innermost sub-disc of `D`, so
`f = e ∘ g` with `g : 𝔻 → 𝔻` injective, `g(∂𝔻) = J := e⁻¹(γ)`, `g(int 𝔻) ∩ e⁻¹(F) = ∅`, and
`g(𝔻)` is the closed sub-disc of `𝔻` bounded by `J`.  `CurvesInterior` says precisely that
`J` misses `∂𝔻`, so `AnnulusSchoenflies` applies to `g` and gives `Θ : 𝔻 ≃ₜ 𝔻` with
`Θ|∂𝔻 = id`, `Θ(g(∂𝔻))` the circle of radius `1/2` (with matching parametrisation) and
`Θ(g(int 𝔻))` the open disc of radius `1/2`.  For `r₀ ∈ (1/2,1)` close enough to `1/2`
(compactness: the other intersection curves are compact and disjoint from `J`) the curve

`z₁ θ := Θ⁻¹ (r₀ • e^{iθ})`,  `h₁ := Θ⁻¹ ∘ (r₀ • ·)`

satisfies the hypotheses of `SurfaceDiscPushOff` with `γ := D.curves j`: `z₁` is off the surface
(it avoids the pull-backs of all the intersection curves), its spanning disc `h₁(𝔻)` contains
`J`-region (it contains the half-disc of radius `1/2` bound by `J`).  A *second* application of
`AnnulusSchoenflies`, now to `h₁`, gives `Θ₁ : 𝔻 ≃ₜ 𝔻` and a sign `s₁ ∈ {1,-1}` with `Θ₁|∂𝔻 = id` and
`Θ₁(h₁(∂𝔻)) = ∂(half-disc)` after the reparametrisation `θ ↦ s₁ θ` (the sign is the orientation of
the embedding `h₁`, and it is absorbed by composing the cap with the disc twist `twistFun s₁` of the
module `Twist`), so that

* the **outer piece** `out z := e (Θ₁⁻¹ z)`, `1/2 ≤ ‖z‖ ≤ 1`, is an embedded annulus in `D` with
  outer boundary `α` and inner boundary the curve `e ∘ z₁`;
* every other intersection curve is in `out`'s image (they are outside `Θ₁⁻¹(half-disc)`);
* the **cap** `cap` given by `SurfaceDiscPushOff` has boundary `e ∘ z₁`, misses `F` in its interior
  and meets the outer piece exactly along `e ∘ z₁`.

Gluing `out` and `cap` along the common boundary curve gives the new embedded disc

`e' z := if ‖z‖ ≤ 1/2 then cap' (dblMap z) else out z`

where `cap' := cap ∘ twistFun s₁` is the cap with the orientation sign of `Θ₁` absorbed and
`dblMap` is the total radial doubling map of the model disc,

with boundary `α`, containing all the other curves, and meeting `F` in the interior only along
those curves.  (`e'` is continuous by pasting on the two closed sets `{‖z‖ ≤ 1/2}` and
`{‖z‖ ≥ 1/2}`, injective because the two pieces meet exactly along their common boundary, and the
last clause comes from `D.covers` together with the fact that the pull-back of the eliminated
curve `γ` lies strictly inside the block of `Θ₁`.)

Nothing outside `Submission/Work/Smooth/SphereJordan/` is modified.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## Two points of the model disc -/

/-- The point `(1/2) • e^{iθ}` of the model disc, the image of the curve `∂𝔻` under the
"half-disc" map of the annulus form of Schoenflies. -/
def halfCirclePoint (θ : ℝ) : Disc :=
  ⟨(1 / 2 : ℂ) * ((Work.Smooth.Jordan.circlePoint θ : Disc) : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Work.Smooth.Jordan.circlePoint_coe,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    norm_num⟩

theorem halfCirclePoint_coe (θ : ℝ) :
    ((halfCirclePoint θ : Disc) : ℂ)
      = (1 / 2 : ℂ) * ((Work.Smooth.Jordan.circlePoint θ : Disc) : ℂ) := rfl

/-- The point `r • e^{iθ}` of the model disc, for `0 ≤ r ≤ 1`. -/
def radiusPoint (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : Disc :=
  ⟨(r : ℂ) * ((Work.Smooth.Jordan.circlePoint θ : Disc) : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Work.Smooth.Jordan.circlePoint_coe,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    have hnorm : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hr0]
    rw [hnorm]
    exact hr1⟩

theorem radiusPoint_coe (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ((radiusPoint r θ hr0 hr1 : Disc) : ℂ)
      = (r : ℂ) * ((Work.Smooth.Jordan.circlePoint θ : Disc) : ℂ) := rfl

/-- The point `r • e^{iθ}` of the model disc, with `r` clamped to `[0,1]`.  This is the
`θ`-parametrisation of the concentric circle of radius `clamp r` of the model disc. -/
def arcPoint (r θ : ℝ) : Disc :=
  radiusPoint (max 0 (min r 1)) θ (le_max_left _ _)
    (max_le (by norm_num) (min_le_right _ _))

theorem arcPoint_coe (r θ : ℝ) :
    ((arcPoint r θ : Disc) : ℂ)
      = ((max 0 (min r 1) : ℝ) : ℂ) * ((Work.Smooth.Jordan.circlePoint θ : Disc) : ℂ) := rfl

theorem arcPoint_eq_radiusPoint (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    arcPoint r θ = radiusPoint r θ hr0 hr1 := by
  apply Subtype.ext
  rw [arcPoint_coe, radiusPoint_coe]
  rw [show max 0 (min r 1) = r from by rw [min_eq_left hr1, max_eq_right hr0]]

theorem norm_arcPoint (r θ : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖((arcPoint r θ : Disc) : ℂ)‖ = r := by
  rw [arcPoint_eq_radiusPoint r θ hr0 hr1, radiusPoint_coe, norm_mul,
    Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hr0]

/-! ## The three named inputs -/

/-- **The annulus form of the Schoenflies theorem, in its *plain* (set-level) form.**

Let `h : 𝔻 → 𝔻` be an embedded closed disc whose boundary circle lies in the *open* unit disc.
Then there is a homeomorphism `Θ` of the closed unit disc such that

* `Θ` fixes the boundary circle pointwise,
* `Θ` carries the disc `h(𝔻)` onto the closed disc of radius `1/2`
  (`(∃ z, h z = x) ↔ ‖Θ x‖ ≤ 1/2`), and the *open* disc `h(int 𝔻)` onto the *open* disc of
  radius `1/2` (`‖z‖ < 1 ↔ ‖Θ (h z)‖ < 1/2`).

This is the classical 2-dimensional theorem behind the "discard a collar" step of Pardon's
cut-and-paste: the region between a Jordan curve inside a disc and the boundary circle of the disc
is a standard annulus.  It carries no clause on the *parametrisation* of the inner boundary circle;
the parametrised form `AnnulusSchoenflies` is derived from it in the module
`Work.Smooth.SphereJordan.Plain` (reparametrising the inner circle by a homeomorphism of `𝔻` that
fixes `∂𝔻` pointwise — an arbitrary homeomorphism of a circle extends to the disc by coning). -/
def PlainAnnulusSchoenflies : Prop :=
  ∀ h : C(Disc, Disc), Function.Injective h →
    (∀ θ : ℝ, ‖((h (Work.Smooth.Jordan.circlePoint θ) : Disc) : ℂ)‖ < 1) →
    ∃ Θ : Disc ≃ₜ Disc,
      (∀ θ : ℝ, Θ (Work.Smooth.Jordan.circlePoint θ) = Work.Smooth.Jordan.circlePoint θ) ∧
      (∀ x : Disc, (∃ z : Disc, h z = x) ↔ ‖((Θ x : Disc) : ℂ)‖ ≤ 1 / 2) ∧
      (∀ z : Disc, ‖((z : Disc) : ℂ)‖ < 1 ↔ ‖((Θ (h z) : Disc) : ℂ)‖ < 1 / 2)

/-- **The annulus form of the Schoenflies theorem.**

Let `h : 𝔻 → 𝔻` be an embedded closed disc whose boundary circle lies in the *open* unit disc.
Then there is a homeomorphism `Θ` of the closed unit disc such that

* `Θ` fixes the boundary circle pointwise,
* `Θ` carries the boundary circle of `h` onto the concentric circle of radius `1/2`.  The
  parametrisation clause is `Θ (h (e^{i s θ})) = (1/2) e^{iθ}` for one of the two signs
  `s = ±1`: a homeomorphism of `𝔻` fixing `∂𝔻` pointwise is orientation-preserving, so it
  cannot reverse the orientation of the inner boundary circle, and which of the two signs
  occurs is the "orientation" of the embedding `h` (the `∨` clause is therefore the sharp
  statement, and both occurrences are needed by the cut-and-paste below),
* `Θ` carries the disc `h(𝔻)` onto the closed disc of radius `1/2`
  (`(∃ z, h z = x) ↔ ‖Θ x‖ ≤ 1/2`), and it carries the *open* disc `h(int 𝔻)` onto the *open*
  disc of radius `1/2` (`‖z‖ < 1 ↔ ‖Θ (h z)‖ < 1/2` for every `z`).  Equivalently, `Θ⁻¹` carries
  the annulus `{1/2 ≤ ‖z‖ ≤ 1}` onto the region of `𝔻` outside the closed disc `h(𝔻)`.
  (The two inequalities are recorded separately, and the strict form is indexed by the points `z`
  of the model disc: the image of the boundary circle of `h` is the *sphere* of radius `1/2`, which
  is not the image of any point of the open disc, so the `∃`-form with `< 1` would be
  contradictory.)

This is the classical 2-dimensional statement behind the "discard a collar" step of Pardon's
cut-and-paste: the region between a Jordan curve inside a disc and the boundary circle of the disc
is a standard annulus, with prescribed behaviour on both boundary circles.  Classically it follows
from the Jordan–Schoenflies theorem in the plane plus the Alexander trick (the homeomorphism can be
chosen to fix a neighbourhood of `∂𝔻`); the parametrisation clause is the usual normalisation of
the Schoenflies homeomorphism on the inner boundary. -/
def AnnulusSchoenflies : Prop :=
  ∀ h : C(Disc, Disc), Function.Injective h →
    (∀ θ : ℝ, ‖((h (Work.Smooth.Jordan.circlePoint θ) : Disc) : ℂ)‖ < 1) →
    ∃ (Θ : Disc ≃ₜ Disc) (s : ℝ), (s = 1 ∨ s = -1) ∧
      (∀ θ : ℝ, Θ (Work.Smooth.Jordan.circlePoint θ) = Work.Smooth.Jordan.circlePoint θ) ∧
      (∀ θ : ℝ, Θ (h (Work.Smooth.Jordan.circlePoint (s * θ))) = halfCirclePoint θ) ∧
      (∀ x : Disc, (∃ z : Disc, h z = x) ↔ ‖((Θ x : Disc) : ℂ)‖ ≤ 1 / 2) ∧
      (∀ z : Disc, ‖((z : Disc) : ℂ)‖ < 1 ↔ ‖((Θ (h z) : Disc) : ℂ)‖ < 1 / 2)

/-- **Local flatness of an embedded disc along a set of its points.**

At every point `x` of `C` (a subset of the image of `e`) the image of the disc looks locally like a
*plane*: some neighbourhood `U` of `x` is mapped by a homeomorphism onto the unit ball of `ℝ³` in
such a way that `U ∩ e(𝔻)` becomes the equatorial plane of the ball.

This is the tameness (PL/smooth regularity) which the classical push-off below needs and which is
**not** a consequence of the structure `Work.Topology.SphereSlicing.SliceDisc`, where the disc is
only assumed to be embedded *continuously*: an arbitrary continuous embedding of a disc can be wild
along a curve, and then no one-sided collar (hence no cap) exists.  It does hold for the smooth
slice discs of Pardon's application, which are the ones the argument uses.  See §8.2 of the
README. -/
def LocallyFlatAlong (e : C(Disc, R3)) (C : Set R3) : Prop :=
  ∀ x : R3, x ∈ C → ∃ (U : Set R3) (_ : IsOpen U) (hx : x ∈ U)
    (Φ : U ≃ₜ Metric.ball (0 : R3) 1),
    Φ ⟨x, hx⟩ = 0 ∧
    ∀ y : R3, y ∈ Metric.ball (0 : R3) 1 →
      ((∃ u : U, (u : R3) ∈ Set.range (fun z : Disc => e z) ∧ (Φ u : R3) = y) ↔ y 2 = 0)

/-- **A tame (locally flat) embedded disc**: the disc is locally flat along the image of its
*interior* (`LocallyFlatAlong`). -/
def LocallyFlat (e : C(Disc, R3)) : Prop :=
  LocallyFlatAlong e ((fun z : Disc => e z) '' {z : Disc | ‖((z : Disc) : ℂ)‖ < 1})

/-- **The push-off of a surface disc** (the "cap" of Pardon's cut-and-paste).

Let `P` be a parametrised torus with surface `F = P.carrier`, let `e : 𝔻 → ℝ³` be an embedded disc
(`D`) whose boundary curve `e ∘ e^{i·}` lies in `F`, let `γ` be a simple closed curve of `F` which

* is contained in `D` (the intersection curve which is being eliminated),
* is **inessential in `F`**: it bounds a disc `E ⊆ F` (`Work.InnermostDisk.BoundsDiscInSurface P γ`),

let `z₁ : ℝ → 𝔻` be a simple closed curve of the model disc, lying in the *open* disc, whose image
under `e` misses `F`, and let `h₁ : 𝔻 → 𝔻` be an embedding with `h₁ (e^{iθ}) = z₁ θ` spanning a
sub-disc whose image under `e` contains `γ`.  Assume moreover the **innermost clause**

`∀ w, ‖w‖ < 1 → e (h₁ w) ∈ F → e (h₁ w) ∈ range γ`

i.e. the disc `e ∘ h₁` (which has boundary the curve `e ∘ z₁` and contains `γ`) meets `F` in its
interior *only along `γ`*.

Then there is an embedded disc `cap` in `ℝ³` with boundary the curve `θ ↦ e (z₁ θ)`, disjoint from
`F` in its interior, and meeting `e(𝔻)` only along its boundary curve.

Geometrically: `z₁` is a push-off of `γ` inside the disc `D`, spanning a disc whose interior
contains no other point of `F`; the surface disc `E ⊆ F` bounded by `γ` is pushed to one side of
`F` and joined to the curve `e ∘ z₁` by a thin collar inside `e(𝔻)`.  This is the classical
tubular-neighbourhood/push-off statement for the embedded surface `F`, in the configuration in
which the innermost argument produces it.

The hypotheses are **necessary** and are isolated here because dropping any of them makes the
statement false (see `Submission/Work/Smooth/SphereJordan/README.md`, §8.2):

* the inessentiality `BoundsDiscInSurface P γ`: if `γ` is essential (a meridian), then the curve
  `e ∘ z₁` is not null-homotopic in `ℝ³ ∖ F`, so no disc whose interior misses `F` spans it;
* the innermost clause: without it, one can take `γ` to be a *constant* curve (which is a
  `ClosedCurve` and is inessential) and `e ∘ z₁` to be the core circle of the solid torus bounded
  by `F`; then `e ∘ z₁` is again not null-homotopic in `ℝ³ ∖ F` and no cap exists.  (The weaker
  statement without the innermost clause is `NaiveSurfaceDiscPushOff` below, and it is *proved*
  false at the standard torus, `not_naiveSurfaceDiscPushOff_standard`.)
* the local flatness `LocallyFlat e`: the cap is a one-sided collar of the disc `e(𝔻)` along the
  curve `e ∘ z₁`, and it is built inside the sub-disc spanned by `h₁`, whose intersection with the
  surface is the curve `γ`; both the collar along `e ∘ z₁` and the crossing at the interior curve
  `γ` require the disc to be tame.  (An earlier formulation asked only for the flatness
  `LocallyFlatAlong e (range (e ∘ z₁))` *along the boundary curve* of the cap; flatness along that
  single curve does not exclude a disc that is wild at the interior crossing curve, so the
  hypothesis is stated for the whole interior image of `e`.)  This hypothesis is *not* automatic:
  the structure `SliceDisc` assumes only that `e` is injective and continuous.  In the constructive
  route of `PastingDerive` it is supplied by the hypothesis `LocallyFlat D.e` on the slice disc
  (see `cutsAlongSubdisc_inside`). -/
def SurfaceDiscPushOff (P : Work.CoreTopology.ParamTorus) : Prop :=
  ∀ (e : C(Disc, R3)), Function.Injective e →
  (∀ θ : ℝ, e (Work.Smooth.Jordan.circlePoint θ) ∈ P.carrier) →
  ∀ (γ : Work.CoreTopology.ClosedCurve P), Set.range γ.γ ⊆ Set.range e →
    Work.InnermostDisk.BoundsDiscInSurface P γ →
  ∀ (z₁ : ℝ → Disc), Continuous z₁ → Function.Periodic z₁ (2 * Real.pi) →
    Set.InjOn z₁ (Set.Ico 0 (2 * Real.pi)) →
    (∀ θ : ℝ, ‖((z₁ θ : Disc) : ℂ)‖ < 1) →
    (∀ θ : ℝ, e (z₁ θ) ∉ P.carrier) →
  ∀ (h₁ : C(Disc, Disc)), Function.Injective h₁ →
    (∀ θ : ℝ, h₁ (Work.Smooth.Jordan.circlePoint θ) = z₁ θ) →
    Set.range γ.γ ⊆ e '' Set.range h₁ →
    (∀ w : Disc, ‖(w : ℂ)‖ < 1 → e (h₁ w) ∈ P.carrier →
      e (h₁ w) ∈ Set.range γ.γ) →
    LocallyFlat e →
    ∃ cap : C(Disc, R3), Function.Injective cap ∧
      (∀ θ : ℝ, cap (Work.Smooth.Jordan.circlePoint θ) = e (z₁ θ)) ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → cap z ∉ P.carrier) ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → cap z ∈ Set.range e →
        cap z ∈ Set.range fun θ : ℝ => e (z₁ θ))

/-- **The *naive* push-off of a surface disc**: `SurfaceDiscPushOff` without the innermost clause.
This statement is **false** (see `Work.Smooth.SphereJordan.not_naiveSurfaceDiscPushOff_standard`):
take `γ` to be the constant curve at a point of `F`, `e` the flat disc of radius `3` in the plane
`{z = 0}` (whose boundary is the outer equator of the standard torus) and `z₁` the circle of radius
`2/3` of the model disc; then `e ∘ z₁` is the core circle of the solid torus bounded by `F`, which
is not null-homotopic in `ℝ³ ∖ F`, so no cap exists although every hypothesis (including the
inessentiality of the constant curve `γ`) holds.  It is recorded here to document that the
innermost clause of `SurfaceDiscPushOff` cannot be dropped. -/
def NaiveSurfaceDiscPushOff (P : Work.CoreTopology.ParamTorus) : Prop :=
  ∀ (e : C(Disc, R3)), Function.Injective e →
  (∀ θ : ℝ, e (Work.Smooth.Jordan.circlePoint θ) ∈ P.carrier) →
  ∀ (γ : Work.CoreTopology.ClosedCurve P), Set.range γ.γ ⊆ Set.range e →
    Work.InnermostDisk.BoundsDiscInSurface P γ →
  ∀ (z₁ : ℝ → Disc), Continuous z₁ → Function.Periodic z₁ (2 * Real.pi) →
    Set.InjOn z₁ (Set.Ico 0 (2 * Real.pi)) →
    (∀ θ : ℝ, ‖((z₁ θ : Disc) : ℂ)‖ < 1) →
    (∀ θ : ℝ, e (z₁ θ) ∉ P.carrier) →
  ∀ (h₁ : C(Disc, Disc)), Function.Injective h₁ →
    (∀ θ : ℝ, h₁ (Work.Smooth.Jordan.circlePoint θ) = z₁ θ) →
    Set.range γ.γ ⊆ e '' Set.range h₁ →
    ∃ cap : C(Disc, R3), Function.Injective cap ∧
      (∀ θ : ℝ, cap (Work.Smooth.Jordan.circlePoint θ) = e (z₁ θ)) ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → cap z ∉ P.carrier) ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → cap z ∈ Set.range e →
        cap z ∈ Set.range fun θ : ℝ => e (z₁ θ))

/-- **Pardon's surgery in the *pinched* configuration** (the second innermost argument when the
innermost intersection curve meets the boundary curve of the slice disc).

Let `D` be a slice disc, `j` an index and `f` the innermost sub-disc of `D` spanning the curve
`γ = D.curves j` (embedded, with boundary `γ`, with interior disjoint from `F`, contained in `D`,
and meeting no other intersection curve), and suppose `γ` meets the boundary curve `α = D.α` of
`D` — the *pinched* configuration, i.e. the negation of the position hypothesis `CurvesInterior`.
Then there is an embedded disc `e'` with the same boundary `α`, containing all the other
intersection curves, whose interior meets `F` only along them.

This is precisely the pinched case of `Work.Topology.Classical.CutsAlongSubdisc`, and it is
Pardon's own argument there: the innermost sub-disc `f` together with the disc `E ⊆ F` bounded by
the inessential curve `γ` forms an embedded `2`-sphere `f ∪ E`, which by **Alexander's theorem**
bounds a ball, and the part of `D` inside that ball is pushed through the sphere by an **isotopy
extension** fixing the boundary curve of `D`.

In the general position of Pardon's application this configuration does not arise: the intersection
curves of a slice disc are components of `F ∩ int D`, hence disjoint from the boundary curve `α`,
so `CurvesInterior P` holds and the *constructive* route of
`Work.Smooth.SphereJordan.PastingDerive` (collar-discard by the annulus form of Schoenflies, then
the cap `SurfaceDiscPushOff`) applies, without Alexander's theorem or isotopy extension.  This
input only covers the configurations in which that construction is provably impossible (the
boundary curve of `D` meets the model curve of `γ`, so no embedding of the standard annulus with
the prescribed boundary values exists; see §6.3 of the README).

**Rejected formulation.** An earlier version of this input asked for a purely *local* modification
of the disc inside a collar `W` of `γ` ("push the disc off the surface through a collar of `γ`",
keeping the disc fixed outside `W`).  That statement is **false**: if the disc meets `F` along `γ`
and crosses from one side of `F` to the other, then the preimage of `W ∩ D` in the disc is an
annulus whose two boundary circles lie on opposite sides of `F`; they are fixed by the requirement
that the disc agree with the original outside `W`, so the modified (connected) piece would have to
avoid `F` while joining the two sides — impossible.  The correct statement instead permits moving
the whole *interior* of the disc, which is what isotopy extension provides. -/
def PinchedPushThrough (P : Work.CoreTopology.ParamTorus) : Prop :=
  ∀ (D : Work.Topology.SphereSlicing.SliceDisc P) (j : D.ι) (f : C(Disc, R3)),
    Function.Injective f →
    (∀ θ : ℝ, f (Work.Smooth.Jordan.circlePoint θ) = (D.curves j).γ θ) →
    (∀ z : Disc, ‖(z : ℂ)‖ < 1 → f z ∉ P.carrier) →
    Set.range f ⊆ Set.range D.e →
    (∀ i : D.ι, i ≠ j →
      Disjoint (Set.range (D.curves i).γ) (f '' {z : Disc | ‖(z : ℂ)‖ < 1})) →
    ¬ Disjoint (Set.range (D.curves j).γ)
      (Set.range fun θ : ℝ => D.e (Work.Smooth.Jordan.circlePoint θ)) →
    ∃ e' : C(Disc, R3),
      Function.Injective e' ∧
      (∀ θ : ℝ, e' (Work.Smooth.Jordan.circlePoint θ) = D.α.γ θ) ∧
      (∀ i : D.ι, i ≠ j → Set.range (D.curves i).γ ⊆ Set.range e') ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → e' z ∈ P.carrier →
        ∃ i : D.ι, i ≠ j ∧ e' z ∈ Set.range (D.curves i).γ)

/-- **A position hypothesis on the slice discs**: the innermost intersection curve of a slice disc
is disjoint from the boundary curve of that disc.  Equivalently: the boundary curve of an innermost
sub-disc of a slice disc lies in the *interior* of the disc.

This holds for the transverse slices of Pardon's application (the components of `S ∩ F` of a
transverse sphere are pairwise disjoint compact curves of the interior of each slice disc), and it
is what excludes the "pinched" configuration in which the innermost curve touches the boundary
curve of the disc; there the collar of the innermost curve in the disc is one-sided and the surgery
needs a different construction.  See `Submission/Work/Smooth/SphereJordan/README.md`. -/
def CurvesInterior (P : Work.CoreTopology.ParamTorus) : Prop :=
  ∀ (D : Work.Topology.SphereSlicing.SliceDisc P) (j : D.ι) (f : C(Disc, R3)),
    Function.Injective f →
    (∀ θ : ℝ, f (Work.Smooth.Jordan.circlePoint θ) = (D.curves j).γ θ) →
    Set.range f ⊆ Set.range D.e →
    Disjoint (Set.range (D.curves j).γ)
      (Set.range fun θ : ℝ => D.e (Work.Smooth.Jordan.circlePoint θ))

end

end Work.Smooth.SphereJordan
