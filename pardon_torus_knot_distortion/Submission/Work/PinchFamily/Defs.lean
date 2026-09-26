import Submission.Work.PinchCounted.Local

/-!
# `Work.PinchFamily` — Pardon's pinching family, and the local residual in its primitive shapes

Entry point: **`import Submission.Work.PinchFamily.All`**.  Namespace `Work.PinchFamily`,
directory `Submission/Work/PinchFamily/`.

## What this chapter is

`Work.PinchCounted.CountedPinch` is the *local* residual of Pardon's counted Lemma 3: at every
configuration carrying the counting data of the crux (`Work.BoxShrink.Pinch.CountingHalf`) there is
a family of regions `region : ℝ → Set R3` from the region inside the box `PBox s c σ` to the two
half-regions cut out by the plane, whose local move at every parameter is a
`Work.PinchCounted.CountedStep` (a transport of the loop content, a change by an open piece whose
loops are matched by loops of a *clean low-count sphere*, or a change by an open piece of vanishing
winding span).

This chapter's job is to say in **primitive** terms what such a family has to be, and to prove
everything about it that can be proved without Pardon's construction of the pinching family of
spheres:

* `Defs.lean` (this file) fixes the vocabulary: the **pinch collar** (`IsPinchCollar`, the piece of
  the surface through which the pinch passes), the **push-off** (`RegionPushOff`, Pardon's
  push-off of the slice in loop-transport form), and the three *residuals* `PinchTransport`,
  `PinchCollarSpan`, `PinchNeckCollar` — each a single `Prop` over the counted configurations of
  the crux, asserting one irreducible geometric input and nothing else;
* `Family.lean` **constructs the family** from either input: from the push-off (the two-piece family
  `boxRegion` for `t < 1` / `halves` for `t ≥ 1`), and from a span-vanishing collar (the three-piece
  family `boxRegion` / `boxRegion ∖ Z` / `halves`), with the endpoints and *every* local move
  verified;
* `Count.lean` proves the counting half of Pardon's Step 2: the **matched** collar has vanishing
  winding span (Pardon's Lemma 2 at the intermediate sphere), and the box sphere is a clean
  low-count sphere for free at every counted configuration — so the `∃ S` of the matched residual
  costs nothing;
* `Reduce.lean` assembles: `countedPinch_of_pinchTransport`,
  `countedPinch_of_pinchCollarSpan`, `countedPinch_of_pinchNeckCollar`, and the transports to
  `Work.BoxShrink.Pinch.CountingHalf`, `Work.BoxShrink.CruxCore`, `Submission.BoxShrinkStatement`
  and the challenge `Submission.pardon_torus_knot_distortion`;
* `Instances.lean` gives the non-vacuity certificates: at every counted configuration whose slice
  trace is **empty**, the residuals hold with `Z = ∅`, so the family exists and `CountedPinch`
  holds there — and the residual is *not* trivial: it implies the span equality
  `W(boxRegion) = W(halves)`, which is a sharp geometric statement (it fails at the standard
  configuration of `Work.BoxShrink.Bubble.cex_not_slicePushOffSpan`).

## The residuals, and what is assumed

| residual | shape | what it asserts |
|---|---|---|
| `PinchTransport` | `RegionPushOff` | Pardon's push-off in loop-transport form: every closed curve of the surface inside the box region is matched, with its winding vector, by a closed curve of the two half-regions, and conversely |
| `PinchCollarSpan` | `SpanCollar` | there is an open piece `Z` of the surface, containing the slice trace and contained in the box region, whose *complement in the box region is again open* (a "collar" that is a union of components), with vanishing winding span |
| `PinchNeckCollar` | `NeckCollar` | the same collar, with the *geometric* reason for the vanishing span: there is a clean low-count sphere whose trace loops match the loops of the collar (Pardon's "the changed piece is a collar of the trace of the intermediate sphere") |

`PinchNeckCollar → PinchCollarSpan → CountedPinch` and `PinchTransport → CountedPinch`; every
implication is a theorem of this chapter.  Nothing else about the pinch is assumed: the families,
their endpoints, their local moves, the counting bookkeeping and all the transports to the challenge
are proved.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.PinchFamily

noncomputable section

/-! ## The two endpoint regions of the pinch -/

/-- The two half-regions of the box, cut out by the plane `{y (σ 2) = c (σ 2) + u}`. -/
abbrev halves (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Work.PinchCounted.PinchSweep.halves P s c σ u

/-- The region of the surface inside the box `PBox s c σ`. -/
abbrev box (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  Work.BoxShrink.Core.boxRegion P s c σ

/-- The trace of the cutting plane inside the box: the slice region. -/
abbrev slice (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  Work.BoxShrink.Core.sliceRegion P s c σ u

/-! ## The pinch collar -/

/-- **A collar of the pinch.**  `Z` is the piece of the surface through which the pinching sphere
passes: it contains the slice trace, it is contained in the region inside the box, it is open in
the surface, and its *complement in the box region is again open* — the last condition says that `Z`
is a union of connected components of the box region, which is exactly what a `CountedStep`'s
disjoint decomposition needs (`Work.SurgeryInvariance.SurgeryStepZero`).

In Pardon's construction the changed piece is the trace of a push-off of the slicing disc; the
complement condition is the honest formalisation of "the region inside the box is cut into the two
half-regions together with the collar". -/
def IsPinchCollar (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (Z : Set R3) : Prop :=
  Work.SurgeryInvariance.IsOpenInCarrier P Z ∧
    slice P s c σ u ⊆ Z ∧
    Z ⊆ box P s c σ ∧
    Work.SurgeryInvariance.IsOpenInCarrier P (box P s c σ \ Z)

theorem isPinchCollar_def (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) {Z : Set R3} :
    IsPinchCollar P s c σ u Z ↔
      Work.SurgeryInvariance.IsOpenInCarrier P Z ∧
        slice P s c σ u ⊆ Z ∧
        Z ⊆ box P s c σ ∧
        Work.SurgeryInvariance.IsOpenInCarrier P (box P s c σ \ Z) := Iff.rfl

namespace IsPinchCollar

variable {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
  {Z : Set R3}

theorem isOpen (h : IsPinchCollar P s c σ u Z) : Work.SurgeryInvariance.IsOpenInCarrier P Z := h.1

theorem slice_subset (h : IsPinchCollar P s c σ u Z) : slice P s c σ u ⊆ Z := h.2.1

theorem subset_box (h : IsPinchCollar P s c σ u Z) : Z ⊆ box P s c σ := h.2.2.1

theorem open_sdiff (h : IsPinchCollar P s c σ u Z) :
    Work.SurgeryInvariance.IsOpenInCarrier P (box P s c σ \ Z) := h.2.2.2

/-- **The box region is the union of the collar with its complement.** -/
theorem box_eq_union (h : IsPinchCollar P s c σ u Z) :
    box P s c σ = (box P s c σ \ Z) ∪ Z := by
  have hsub : Z ⊆ box P s c σ := h.subset_box
  ext y
  constructor
  · intro hy
    by_cases hyZ : y ∈ Z
    · exact Set.mem_union_right _ hyZ
    · exact Set.mem_union_left _ ⟨hy, hyZ⟩
  · rintro (⟨hy, -⟩ | hyZ) <;> [exact hy; exact hsub hyZ]

/-- **The two pieces of the collar decomposition are disjoint.** -/
theorem disjoint_sdiff (h : IsPinchCollar P s c σ u Z) : Disjoint (box P s c σ \ Z) Z := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hx⟩ hxZ
  exact hx hxZ

/-- **The complement of the collar inside the box is contained in the two half-regions.** -/
theorem sdiff_subset_halves (h : IsPinchCollar P s c σ u Z) :
    box P s c σ \ Z ⊆ halves P s c σ u := by
  intro y hy
  have hybox : y ∈ box P s c σ := hy.1
  by_contra hyh
  have hyslice : y ∈ slice P s c σ u := by
    rcases Work.BoxShrink.Core.mem_boxRegion.mp hybox with ⟨hyc, hyb⟩
    have hne : y (σ 2) = c (σ 2) + u := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hyh (Set.mem_union_right _ (Work.BoxShrink.Core.mem_lowerRegion.mpr ⟨hyc, hyb, hlt⟩))
      · exact hyh (Set.mem_union_left _ (Work.BoxShrink.Core.mem_upperRegion.mpr ⟨hyc, hyb, hgt⟩))
    exact Work.BoxShrink.Core.mem_sliceRegion.mpr ⟨hyc, hyb, hne⟩
  exact hy.2 (h.slice_subset hyslice)

end IsPinchCollar

/-! ## The push-off -/

/-- **Pardon's push-off, in loop-transport form.**  Every closed curve of the surface inside the two
half-regions is matched, with its winding vector, by a closed curve inside the box region, and
conversely.  This is the "isotopy-extension statement behind the transport": it says that the slice
trace carries no loop content that the two half-regions do not already carry.

It is the *weakest* single statement of what Pardon's Step 2 delivers at a counted configuration:
`Work.PinchFamily.exists_region_of_regionPushOff` turns it into the family of `CountedPinch`. -/
def RegionPushOff (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  Work.SurgeryInvariance.RegionEquivalent P (halves P s c σ u) (box P s c σ)

/-- The push-off is symmetric in its two arguments (the relation `RegionEquivalent` is). -/
theorem regionPushOff_comm (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    RegionPushOff P s c σ u ↔
      Work.SurgeryInvariance.RegionEquivalent P (box P s c σ) (halves P s c σ u) :=
  Work.SurgeryInvariance.RegionEquivalent.comm

/-! ## The counted configuration of the crux, as a shell -/

/-- **The shell of Pardon's counted configuration.**  `Residual Q` says that at every configuration
carrying the counting data of the crux — the knot data (`p`, `q`, `ψ`, `K`, the distortion bound
`d`, the smallness `countConst · d < min p q`), the clean cut-and-paste
(`Work.InnermostDisk.CleansDiscs`), the swept box with an essential loop (`HasEssBox`), the sphere
in general position (`SlicedSphere`) and the two intersection counts — the predicate `Q` holds at
that configuration.

The binders are exactly those of `Work.PinchCounted.CountedPinch`, so that the residuals of this
chapter are directly comparable with it (`workPinchCounted_countedPinch_eq`). -/
def Residual (Q : (P : Work.CoreTopology.ParamTorus) → Work.CoreTopology.ClosedCurve P →
    ℝ → R3 → Equiv.Perm (Fin 3) → ℝ → Prop) : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Smooth.Morse.torus ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Smooth.Morse.torus ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          Q (Work.Smooth.Morse.torus ψ)
            (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
              (Work.CoreTopology.standardCurve p q)) s c σ u

/-! ## The three residuals -/

/-- **The local family of Pardon's counted Lemma 3** (the body of `Work.PinchCounted.CountedPinch`):
a family of regions from the region inside the box to the two half-regions together with an open
piece of vanishing span, whose local move at every parameter is a `CountedStep`. -/
def LocalFamilyBody (P : Work.CoreTopology.ParamTorus) (β : Work.CoreTopology.ClosedCurve P)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ∃ region : ℝ → Set R3,
    region 0 = box P s c σ ∧
    (∃ Z : Set R3,
      Work.SurgeryInvariance.IsOpenInCarrier P Z ∧
      Work.SurgeryInvariance.WindingSpan P Z = ⊥ ∧
      Disjoint (halves P s c σ u) Z ∧
      region 1 = halves P s c σ u ∪ Z) ∧
    ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r - t| < ε →
      Work.PinchCounted.CountedStep P β (region t) (region r)

/-- **The counting configuration of the crux is exactly `Work.PinchCounted.CountedPinch`**: the
residual of this chapter with the body `LocalFamilyBody` is the previous chapter's `CountedPinch`,
binder for binder. -/
theorem countedPinch_eq_residual_localFamilyBody :
    Work.PinchCounted.CountedPinch = Residual LocalFamilyBody := rfl

/-- The *body* of `Work.PinchCounted.CountedPinch` at every counted configuration. -/
def PinchFamilyResidual : Prop := Residual LocalFamilyBody

/-- `CountedPinch` is the family residual. -/
theorem countedPinch_iff_pinchFamilyResidual :
    Work.PinchCounted.CountedPinch ↔ PinchFamilyResidual := by
  rw [countedPinch_eq_residual_localFamilyBody]; rfl

/-! ### The collar residuals -/

/-- The **span form** of the collar: an open piece of the surface containing the slice trace, inside
the box region, with open complement in the box region, and vanishing winding span. -/
def SpanCollarBody (P : Work.CoreTopology.ParamTorus) (_β : Work.CoreTopology.ClosedCurve P)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ∃ Z : Set R3, IsPinchCollar P s c σ u Z ∧ Work.SurgeryInvariance.WindingSpan P Z = ⊥

/-- The **matched form** of the collar (Pardon's own description of the changed piece): the loops
of the collar are matched, with their winding vectors, by loops of a clean sphere meeting the knot
`β` fewer than `I(F,β)` times. -/
def NeckCollarBody (P : Work.CoreTopology.ParamTorus) (β : Work.CoreTopology.ClosedCurve P)
    (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  ∃ Z S : Set R3, IsPinchCollar P s c σ u Z ∧
    Work.InnermostDisk.CleansInSphere P S ∧
    Set.encard (Set.range β.γ ∩ S) < Work.CoreTopology.pardonsI P β ∧
    (∀ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ Z) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ' t ∈ S) ∧
        Work.SurgeryInvariance.windingOf P γ' = Work.SurgeryInvariance.windingOf P γ)

/-! ### The residuals -/

/-- **Residual 1: the push-off.**  At every counted configuration of the crux, every closed curve of
the surface inside the box region is matched, with its winding vector, by a closed curve of the two
half-regions (and conversely). -/
def PinchTransport : Prop := Residual fun _P _β s c σ u => RegionPushOff _P s c σ u

/-- **Residual 2: the collar, in span form.**  At every counted configuration of the crux there is
a collar of the pinch whose winding span vanishes. -/
def PinchCollarSpan : Prop := Residual SpanCollarBody

/-- **Residual 3: the collar, in matched form.**  At every counted configuration of the crux there
is a collar of the pinch whose loops are matched by loops of a clean low-count sphere — Pardon's
geometric description of the changed piece of his pinch. -/
def PinchNeckCollar : Prop := Residual NeckCollarBody

end

end Work.PinchFamily
