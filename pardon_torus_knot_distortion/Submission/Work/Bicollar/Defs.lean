import Submission.Work.Collar3D.Classical
import Submission.Work.Alexander3D.Defs
import Submission.Work.Topology.Classical.Defs

/-!
# `Work.Bicollar` — the bicollar (regular-neighbourhood) theorems for locally flat surfaces

This is the chapter of **regular neighbourhood / bicollar theorems** for a locally flat surface
`F ⊆ ℝ³`: the ambient product structure of the pair `(ℝ³, F)` along a curve (or a disc, or a
sphere) of `F`.  It is the area of the Pardon development listed in
`Submission/Work/Bicollar/README.md`; the four named classical inputs it owns are the workspace's

```lean
Work.Collar3D.RegularNeighbourhoodCurve   -- a framed curve of a locally flat surface has a collar
Work.Alexander3D.InessentialCurveCollar   -- an inessential curve of a locally flat surface has a collar
Work.Collar3D.RegularNeighbourhoodDisc    -- a locally flat embedded disc has a bicollar
Work.Collar3D.SphereBoundsBall            -- an embedded 2-sphere bounds a thick compact region
```

## What this file defines

* the aliases under which the chapter refers to the workspace's vocabulary (`R3`, `Disc`, `Circle`,
  `circlePoint`, `Collar`, `DiscCollar`, `IsCircleCurve`, the local-flatness predicates);
* `Work.Bicollar.IsInessentialCurve` — the *inessentiality* of a curve of `F` in the shape in
  which `InessentialCurveCollar` consumes it: a continuous disc of `F` spanned on the curve;
* `Work.Bicollar.ProductAlong` — a **product structure of the pair `(ℝ³, F)` over a piece `A ⊆ F`**:
  an open neighbourhood `U` of `A` and a homeomorphism `U ≃ₜ A × ℝ` carrying `A` to `A × {0}` and
  `F ∩ U` to the zero level.  This is the "relative regular neighbourhood" form of a collar, and
  `Work.Bicollar.hasProductAlong_iff_hasCollar` proves it equivalent to the collar form;
* `Work.Bicollar.HalfCollar` — the collar of a surface **with boundary** along its boundary curve
  (the pair `(ℝ³, F)` modelled on `(ℝ³, half-plane)`), the datum that the disc collar induces on
  the boundary circle;
* the named inputs of the chapter, each stated in `ℝ³` alone (`Work.Bicollar.InessentialFraming`,
  `Work.Bicollar.DiscBoundaryCollar`, `Work.Bicollar.DiscInteriorGluing`,
  `Work.Bicollar.BrouwerFixedPointBall3`), with the reductions proved in the other modules.

Nothing outside `Submission/Work/Bicollar/` is modified.
-/

open Set

namespace Work.Bicollar

noncomputable section

/-! ## The vocabulary of the workspace, under the chapter's names -/

/-- The ambient Euclidean space `ℝ³`. -/
abbrev R3 : Type := Work.Collar3D.R3

/-- The model circle `S¹`. -/
abbrev Circle : Type := Work.Collar3D.Circle

/-- The model disc `𝔻 = {z : ℂ | ‖z‖ ≤ 1}`. -/
abbrev Disc : Type := Work.Collar3D.Disc

/-- The standard parametrisation `θ ↦ e^{iθ}` of the circle. -/
abbrev circlePoint (θ : ℝ) : Circle := Work.Collar3D.circlePoint θ

/-- The round closed unit ball. -/
abbrev Ball3 : Set R3 := Metric.closedBall (0 : R3) 1

/-- The round unit `2`-sphere. -/
abbrev Sphere2 : Set R3 := Metric.sphere (0 : R3) 1

/-- A simple closed curve, in the convention of the workspace. -/
abbrev IsCircleCurve (γ : ℝ → R3) : Prop := Work.Collar3D.IsCircleCurve γ

/-- The collar of the surface `F` along the curve `γ`. -/
abbrev Collar (F : Set R3) (γ : ℝ → R3) : Type := Work.Collar3D.Collar F γ

/-- There is a collar of `F` along `γ`. -/
abbrev HasCollar (F : Set R3) (γ : ℝ → R3) : Prop := Work.Collar3D.HasCollar F γ

/-- The collar (bicollar) of the embedded disc `e`. -/
abbrev DiscCollar (e : C(Disc, R3)) : Type := Work.Collar3D.DiscCollar e

/-- There is a bicollar of `e`. -/
abbrev HasDiscCollar (e : C(Disc, R3)) : Prop := Work.Collar3D.HasDiscCollar e

/-- **The framing of a curve of a surface**: an annular piece `A ⊆ F` containing `γ` as its core. -/
abbrev Framing (F : Set R3) (γ : ℝ → R3) : Prop := Work.Collar3D.HasAnnularNeighbourhood F γ

/-- Local flatness (tameness) of `F` at `x`. -/
abbrev LocallyFlatSetAt (F : Set R3) (x : R3) : Prop := Work.Smooth.PushThrough3D.LocallyFlatSetAt F x

/-- Local flatness (tameness) of `F`. -/
abbrev LocallyFlatSet (F : Set R3) : Prop := Work.Smooth.PushThrough3D.LocallyFlatSet F

/-- A tame (locally flat) embedded disc. -/
abbrev TameDisc (e : C(Disc, R3)) : Prop := Work.Smooth.SphereJordan.LocallyFlat e

/-- An embedded `2`-sphere. -/
abbrev IsEmbeddedSphere (S : Set R3) : Prop := Work.InnermostDisk.IsEmbeddedSphere S

/-! ## Inessential curves -/

/-- **`γ` is inessential in `F`**: there is a continuous disc of `F` spanned on `γ`.  This is the
hypothesis of the workspace's `Work.Alexander3D.InessentialCurveCollar` (there it is written out;
here it is a named predicate so that its transport and its instances can be stated).

The disc `Σ` is *not* assumed to be embedded: this is the honest shape of what Pardon's innermost
argument produces (the intersection curve bounds a disc of the surface), and the classical content
is that the framing — a two-sided neighbourhood of `γ` in `F` — follows from it. -/
def IsInessentialCurve (F : Set R3) (γ : ℝ → R3) : Prop :=
  ∃ Sig : C(Disc, R3), (∀ θ : ℝ, Sig (Work.Smooth.Jordan.circlePoint θ) = γ θ) ∧
    ∀ z : Disc, Sig z ∈ F

/-- The image of a span of an inessential curve lies in the surface. -/
theorem IsInessentialCurve.range_subset {F : Set R3} {γ : ℝ → R3}
    (h : IsInessentialCurve F γ) : Set.range γ ⊆ F := by
  obtain ⟨Sig, hbd, hmem⟩ := h
  rintro x ⟨θ, rfl⟩
  rw [← hbd θ]
  exact hmem _

/-! ## Product structures of the pair over a piece of the surface -/

/-- **A product structure of the pair `(ℝ³, F)` over a piece `A ⊆ F`.**

This is the *relative regular neighbourhood* of the surface over the piece `A`: an open
neighbourhood `U` of `A`, a homeomorphism `Φ : U ≃ₜ A × ℝ` carrying `A` to `A × {0}`, and with
`F ∩ U` the zero level set of the second coordinate.  In other words the pair `(U, F ∩ U)` is the
product of the pair `(A, A)` with the normal line.

`Work.Bicollar.hasProductAlong_iff_hasCollar` proves that, when `A` is an annulus containing `γ`
as its core, this is exactly the collar `Work.Collar3D.Collar F γ` — so the collar theorem can be
stated, proved and consumed in both vocabularies. -/
structure ProductAlong (F : Set R3) (A : Set R3) where
  /-- the piece lies in the surface -/
  hA : A ⊆ F
  /-- the open neighbourhood of the piece -/
  U : Set R3
  /-- it is open -/
  isOpen_U : IsOpen U
  /-- it contains the piece -/
  hAU : A ⊆ U
  /-- the product chart -/
  Φ : U ≃ₜ A × ℝ
  /-- the chart is the identity onto the middle sheet on the piece -/
  Φ_apply : ∀ (a : R3) (ha : a ∈ A), Φ ⟨a, hAU ha⟩ = (⟨a, ha⟩, 0)
  /-- the chart carries the surface onto the middle sheet -/
  Φ_mem : ∀ u : U, ((u : R3) ∈ F ↔ (Φ u).2 = 0)

/-- **The pair `(ℝ³, F)` is a product over `A`.** -/
def HasProductAlong (F : Set R3) (A : Set R3) : Prop := Nonempty (ProductAlong F A)

/-! ## Half-collars: the collar of a surface with boundary along its boundary curve -/

/-- **A half-collar of `F` along `γ`**: the pair `(ℝ³, F)` is modelled on the pair
`(ℝ³, half-plane)` along `γ`.

`U` is open and contains `γ`, and `Φ : U ≃ₜ S¹ × ℝ × ℝ` carries `γ` to the core circle
`S¹ × {0} × {0}` and `F ∩ U` onto the *closed half-sheet* `S¹ × [0,∞) × {0}`.  Thus `γ` is the
boundary curve of the surface piece `F ∩ U`, the surface lying entirely on the `s ≥ 0` side.

The main instance is the boundary curve of a disc (module `Work.Bicollar.Disc`): a disc collar of
`e` restricts to a half-collar of `Set.range e` along `e ∘ circlePoint`. -/
structure HalfCollar (F : Set R3) (γ : ℝ → R3) where
  /-- the open neighbourhood of the curve -/
  U : Set R3
  /-- it is open -/
  isOpen_U : IsOpen U
  /-- it contains the curve -/
  mem_γ : ∀ θ : ℝ, γ θ ∈ U
  /-- the product chart of the ambient space -/
  Φ : U ≃ₜ Circle × ℝ × ℝ
  /-- the chart carries the curve to the boundary circle of the half-sheet -/
  Φ_γ : ∀ θ : ℝ, Φ ⟨γ θ, mem_γ θ⟩ = (circlePoint θ, 0, 0)
  /-- the chart carries the surface onto the half-sheet -/
  Φ_F : ∀ u : U, ((u : R3) ∈ F ↔ (Φ u).2.2 = 0 ∧ 0 ≤ (Φ u).2.1)

/-- **There is a half-collar of `F` along `γ`.** -/
def HasHalfCollar (F : Set R3) (γ : ℝ → R3) : Prop := Nonempty (HalfCollar F γ)

/-! ## The named inputs of the chapter -/

/-- **The framing of an inessential curve** (the two-dimensional half of the regular-neighbourhood
theorem): a simple closed curve of a locally flat surface which is spanned by a disc of the surface
has a two-sided (annular) neighbourhood in the surface.

This is the content of the regular-neighbourhood theorem that lives purely in the surface: the
normal bundle of `γ` in `F` is the restriction of the tangent bundle of `F`, hence trivial as soon
as `γ` is null-homotopic in `F`; and a curve of `F` with trivial normal bundle is two-sided, i.e.
has an annular neighbourhood.  It is the hypothesis of `Work.Collar3D.RegularNeighbourhoodCurve`,
and `Work.Bicollar.inessentialCurveCollar_of` proves that with `RegularNeighbourhoodCurve` it gives
`Work.Alexander3D.InessentialCurveCollar`.

Non-vacuity is proved in `Work.Bicollar.Nonvacuity` (the unit circle of the plane). -/
def InessentialFraming : Prop :=
  ∀ (F : Set R3) (γ : ℝ → R3), LocallyFlatSet F → IsCircleCurve γ → (∀ θ : ℝ, γ θ ∈ F) →
    IsInessentialCurve F γ → Framing F γ

/-- **The framing of an inessential curve, in the *embedded* form**: a simple closed curve of a
locally flat surface which is the boundary of an **embedded** disc of the surface has a two-sided
(annular) neighbourhood in the surface.

This is `Work.Bicollar.InessentialFraming` with the stronger hypothesis that the spanning disc is
embedded.  It is *strictly weaker* as an input (its hypothesis is stronger), and it is the case
that Pardon's argument supplies: the innermost intersection curve bounds an *embedded* disc of the
surface (`Work.InnermostDisk.BoundsDiscInSurface`).  Non-vacuity: the unit circle of the plane. -/
def InessentialFramingEmbedded : Prop :=
  ∀ (F : Set R3) (γ : ℝ → R3) (Sig : C(Disc, R3)), LocallyFlatSet F → IsCircleCurve γ →
    Function.Injective Sig → (∀ θ : ℝ, Sig (Work.Smooth.Jordan.circlePoint θ) = γ θ) →
    (∀ z : Disc, Sig z ∈ F) → Framing F γ

/-- **The regular-neighbourhood theorem along an inessential curve, in the *embedded* form**: the
statement of `Work.Alexander3D.InessentialCurveCollar` with the spanning disc required to be
*embedded*.

It is *strictly weaker* as an input (it has one hypothesis more), it follows from the workspace's
`Work.Alexander3D.InessentialCurveCollar` (`Work.Bicollar.inessentialCurveCollarEmbedded_of_inessentialCurveCollar`),
and it is the form in which Pardon's innermost argument produces the curve: the innermost
intersection curve bounds an *embedded* disc of the surface.  It follows from the two inputs
`Work.Collar3D.RegularNeighbourhoodCurve` and `Work.Bicollar.InessentialFramingEmbedded`
(`Work.Bicollar.inessentialCurveCollarEmbedded_of`). -/
def InessentialCurveCollarEmbedded : Prop :=
  ∀ (F : Set R3) (γ : ℝ → R3),
    LocallyFlatSet F → IsCircleCurve γ → (∀ θ : ℝ, γ θ ∈ F) →
    (∃ Sig : C(Disc, R3), Function.Injective Sig ∧
      (∀ θ : ℝ, Sig (Work.Smooth.Jordan.circlePoint θ) = γ θ) ∧ ∀ z : Disc, Sig z ∈ F) →
    HasCollar F γ

/-- **The boundary model of a tame disc**: a tame embedded disc has a *half-collar* of its image
along its boundary curve — equivalently, the pair `(ℝ³, e(𝔻))` is modelled on `(ℝ³, half-plane)`
along the curve `θ ↦ e (e^{iθ})`.

This is the first half of the decomposition of `Work.Collar3D.RegularNeighbourhoodDisc`: it is a
statement about a neighbourhood of the *boundary curve* only.  It is *strictly weaker* than the
disc collar (a disc collar restricts to it, `Work.Bicollar.discBoundaryModel_of`), and together
with `Work.Bicollar.DiscInteriorGluing` it gives the disc collar
(`Work.Bicollar.regularNeighbourhoodDisc_of`).  Non-vacuity: the flat model disc
(`Work.Collar3D.hasDiscCollar_modelDisc` through `Work.Bicollar.discBoundaryModel_of`). -/
def DiscBoundaryModel : Prop :=
  ∀ e : C(Disc, R3), TameDisc e →
    HasHalfCollar (Set.range (fun z : Disc => e z)) (fun θ : ℝ => e (Work.Smooth.Jordan.circlePoint θ))

/-- **The gluing half of the disc-collar theorem**: a tame disc whose boundary curve is
half-collared has a bicollar.

This is the second half of the decomposition of `Work.Collar3D.RegularNeighbourhoodDisc`: given the
product structure of the pair along the boundary curve and the local flatness of the disc in its
interior, the two product structures glue over the *whole* disc.  It is *strictly weaker* than the
disc collar (which implies it trivially, `Work.Bicollar.discInteriorGluing_of`), and together with
`Work.Bicollar.DiscBoundaryModel` it gives the disc collar
(`Work.Bicollar.regularNeighbourhoodDisc_of`). -/
def DiscInteriorGluing : Prop :=
  ∀ e : C(Disc, R3), TameDisc e →
    HasHalfCollar (Set.range (fun z : Disc => e z)) (fun θ : ℝ => e (Work.Smooth.Jordan.circlePoint θ)) →
    HasDiscCollar e

/-- **Brouwer's fixed point theorem for the round closed ball of `ℝ³`**: every continuous
self-map of the closed unit ball has a fixed point.

This is the standard classical theorem that pins down the remaining clause of
`Work.Collar3D.SphereBoundsBall`: it is what rules out the collapse of a compact region with
frontier an embedded sphere onto that sphere
(`Work.Bicollar.not_exists_homeo_ball_sphere`, `Work.Bicollar.sphereBoundsBall_of`).  Mathlib has
neither it nor its equivalent, the no-retraction theorem for the sphere in the ball. -/
def BrouwerFixedPointBall3 : Prop := ∀ f : C(Ball3, Ball3), ∃ x : Ball3, f x = x

/-! ## The model disc under a homothety -/

/-- **Multiplication of the model disc by a number of `[0,1]`**, as a continuous map
`𝔻 → 𝔻`.  It is the contraction whose image is the closed sub-disc of radius `r`, and it is
the map under which a sub-disc of a collared disc is cut out. -/
noncomputable def discSmul (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : C(Disc, Disc) where
  toFun z := ⟨(r : ℂ) * (z : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_mul]
    have hz : ‖(z : ℂ)‖ ≤ 1 := by
      have h := z.2
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact h
    have hr : ‖((r : ℝ) : ℂ)‖ = r := by simp [abs_of_nonneg h0]
    rw [hr]
    calc r * ‖(z : ℂ)‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hz h0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ = 1 := by norm_num⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val

@[simp] theorem discSmul_apply (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (z : Disc) :
    ((discSmul r h0 h1 z : Disc) : ℂ) = (r : ℂ) * (z : ℂ) := rfl

end

end Work.Bicollar
