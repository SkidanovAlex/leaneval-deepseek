import Mathlib
import Submission.Work.Drive.EpsFormSphere.Defs
import Submission.Work.Drive.InterfacesD
import Submission.Work.SurgeryInvariance.SphereSweep

/-!
# The sideways slab sweep: the design of field 2 (Pardon's Lemma 3)

This module records the **sideways sweep** into which the project lead reformulated Pardon's pinching
argument (message of 2026-09-24), so that its four analytic/geometric pieces can be delegated and
machine-checked separately.

## The design (Pardon's `doublebubble`, with the family fixed)

Take a thin slab `Z_h = {y : |y (σ 2) - (c (σ 2) + u)| < h} ∩ PBox` around the cutting plane (`h`
small), a *generic* horizontal direction `ℓ : R3 →L[ℝ] ℝ` (a linear functional whose level sets are
transverse to the slab's faces and whose restrictions to the surface are Morse), and sweep the flat
wall

  `wall lam = Z_h ∩ {y : ℓ y < lam}`

sideways through the box: the region of the sweep is

  `sideRegion lam = P ∩ (PBox \ wall lam)`.

* At the start (`lam` below `min ℓ` on the box) nothing is removed: `sideRegion = boxRegion`.
* At the end (`lam` above `max ℓ`) the whole slab is removed: `sideRegion = boxRegion \ Z_h`, which,
  for `h < ε`, lies within the `ε`-neighbourhood of `int(H₁) ∪ int(H₂)` — the ε-clause.

The point of the sideways sweeping (in contrast to the height-wise slab of `Work.Step2.pinchRegion`)
is that the wall moves *transversally* through the slab: `P ∩ sideRegion lam` changes at the finitely
many **critical values of `ℓ` on the surface-with-boundary `P ∩ closure (Z_h)`**, and at each of them
a *single handle* (index `0`, `1` or `2`, interior or boundary) is attached or removed, so the
`H₁`-image rank changes by at most one.  Between critical values the regions are isotopic (the flow
of a gradient-like field of `ℓ`), so the winding span is constant; and at a *regular* level the trace
`∂(sideRegion lam) ∩ P` meets the knot in fewer than `I(F,β)` points (the count `|S ∩ β| + 2|D ∩ β|`),
so Pardon's `mustbeinessential` makes the whole trace inessential, and Pardon's dichotomy pins the
rank to `0` or `2g`.  Hence the rank is constant from the box region to the end region, and the end
region's decomposition into its upper and lower pieces finishes the argument.

## Contents

* the definitions `slabZ`, `wallRegion`, `sideRegion` of the family;
* `SideSweepData P s c σ u` — the four ingredients of the argument (regularity between critical
  values, the cross-critical jump of the rank by at most one, Pardon's dichotomy at the regular
  levels, and the two endpoints);
* `SideSweepExists` — the residual: such data exist at every configuration carrying the counting data
  of the crux (this is P1 + P2 + P3 + P4 of the design);
* `span_eq_of_regular`, `span_eq_of_sideSweep`, `thickHalf_of_sideSweep` (the assembly P5, done
  here): from the data, the ε-form `ThickHalf` follows.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.Drive.EpsSphere

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **The thin slab** of half-width `h` around the cutting plane
`{y : y (σ 2) = c (σ 2) + u}`. -/
def slabZ (c : R3) (σ : Equiv.Perm (Fin 3)) (u h : ℝ) : Set R3 :=
  {y : R3 | |y (σ 2) - (c (σ 2) + u)| < h}

/-- **The moving wall**: the part of the slab in front of the level `lam` of the horizontal
functional `ℓ`. -/
def wallRegion (c : R3) (σ : Equiv.Perm (Fin 3)) (u h : ℝ) (ℓ : R3 →L[ℝ] ℝ)
    (lam : ℝ) : Set R3 :=
  slabZ c σ u h ∩ {y : R3 | ℓ y < lam}

/-- **The region of the sideways sweep**: the box region with the part of the slab behind the wall
removed. -/
def sideRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) : Set R3 :=
  P.carrier ∩ (Submission.PBox s c σ \ wallRegion c σ u h ℓ lam)

/-- **The four ingredients of the sideways sweep** (P1–P4 of the design), at one configuration.

The family `sideRegion · lam` sweeps the box region to the box region with the slab removed; `exc` is
the finite set of critical values of `ℓ` on `P ∩ closure (slabZ)`, `lam0` and `lam1` lie below and above
all of them, and:

* `regular_span` — between two levels with no critical value in between, the winding span of the
  region is constant (P2: the regions are isotopic by the flow of a gradient-like field of `ℓ`);
* `jump` — across a single critical value the `H₁`-image rank changes by at most one (P3: a single
  handle is attached or removed);
* `dichotomy` — at a regular level the rank is `0` or `2g`, i.e. the winding span is `⊥` or `⊤`
  (P4: the count at the intermediate sphere plus Pardon's `mustbeinessential` and his dichotomy). -/
structure SideSweepData (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) where
  /-- the half-width of the slab -/
  h : ℝ
  /-- it is positive (and, in the application, smaller than the ε-margin of the crux) -/
  hpos : 0 < h
  /-- the horizontal functional -/
  ℓ : R3 →L[ℝ] ℝ
  /-- the lower end of the sweep -/
  lam0 : ℝ
  /-- the upper end of the sweep -/
  lam1 : ℝ
  /-- the sweep is nondegenerate -/
  hlt : lam0 < lam1
  /-- the critical values of the horizontal functional on the surface inside the slab -/
  exc : Finset ℝ
  /-- they all lie strictly inside the swept interval -/
  exc_mem : ∀ t ∈ exc, lam0 < t ∧ t < lam1
  /-- at the lower end nothing is removed yet -/
  start : sideRegion P s c σ u h ℓ lam0 = Work.BoxShrink.Core.boxRegion P s c σ
  /-- at the upper end the whole slab is removed -/
  finish : sideRegion P s c σ u h ℓ lam1 =
    Work.BoxShrink.Core.boxRegion P s c σ \ slabZ c σ u h
  /-- **P2**: between two levels with no critical value in between, the winding span is constant -/
  regular_span : ∀ lam lam' : ℝ, lam0 ≤ lam → lam ≤ lam' → lam' ≤ lam1 →
    (∀ t ∈ exc, t < lam ∨ lam' < t) →
    Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ lam) =
      Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ lam')
  /-- **P3**: across a single critical value the `H₁`-image rank changes by at most one -/
  jump : ∀ lam ∈ exc, ∀ mu nu : ℝ, lam0 ≤ mu → mu < lam → lam < nu → nu ≤ lam1 →
    (∀ t ∈ exc, t < mu ∨ t = lam ∨ nu < t) →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ mu)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ nu)) + 1 ∧
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ nu)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ mu)) + 1
  /-- **P4**: at a regular level the winding span is `⊥` or `⊤` (Pardon's dichotomy) -/
  dichotomy : ∀ lam : ℝ, lam0 ≤ lam → lam ≤ lam1 → (∀ t ∈ exc, t ≠ lam) →
    Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ lam) = ⊥ ∨
      Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ lam) = ⊤

/-- **The residual of the design (P1–P4)**: at every configuration carrying the counting data of the
crux there is a sideways sweep of the four ingredients, with the slab narrow enough to be inside the
`ε`-neighbourhood of the two half-regions. -/
def SideSweepExists : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          Nonempty (SideSweepData (torusOf ψ) s c σ u)


end

end Work.Drive.EpsSphere

namespace Work.Drive.EpsSphere

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- **P1 + P2 of the design (the geometry of the swing)**: for the counted configurations there are
a slab width `h > 0`, a horizontal functional `ℓ`, endpoints `lam0 < lam1` and a finite set `exc` of
critical values inside the swept interval such that the sweep starts at the box region, ends at the
box region with the slab removed, and has constant winding span between two levels with no critical
value in between.

P1 is the existence of the finite critical set (generic `ℓ` and `h`: finitely many nondegenerate
critical points of `ℓ` on `P ∩ closure (slabZ)`, the surface transverse to the wall and to the two
slab faces there); P2 is the constancy of the span between critical values (the isotopy sliding the
wall, i.e. the flow of a gradient-like field of `ℓ`). -/
def SwingGeometry (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∃ (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
    0 < h ∧ lam0 < lam1 ∧ (∀ t ∈ exc, lam0 < t ∧ t < lam1) ∧
    sideRegion P s c σ u h ℓ lam0 = Work.BoxShrink.Core.boxRegion P s c σ ∧
    sideRegion P s c σ u h ℓ lam1 =
      Work.BoxShrink.Core.boxRegion P s c σ \ slabZ c σ u h ∧
    (∀ lam lam' : ℝ, lam0 ≤ lam → lam ≤ lam' → lam' ≤ lam1 →
      (∀ t ∈ exc, t < lam ∨ lam' < t) →
      Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ lam) =
        Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ lam'))

/-- **P3 + P4 of the design (the counting half)**, for the data produced by `SwingGeometry`: across
each of the critical values the `H₁`-rank changes by at most one, and at every regular level the
winding span is `⊥` or `⊤` (Pardon's dichotomy, from the count at the intermediate sphere plus
`mustbeinessential`).

WARNING (audit of 2026-09-24).  As written this is universally quantified over `(h, ℓ, lam0, lam1,
exc)` with only the loose side conditions `0 < h`, `lam0 < lam1`, `exc ⊆ (lam0, lam1)`, and it is
**false for non-generic data**: for the *constant* functional `ℓ = 0` with `exc = {0}` it demands a
rank jump of at most one between `lam0 < 0` and `lam1 > 0`, where the regions are `boxRegion` and
`boxRegion \ slabZ` — a jump of two at the configurations recorded in `DESIGN.md`.  A correct P3+P4
must quantify only over data whose functional `ℓ` is *Morse on the surface inside the slab* and whose
`exc` is its set of critical values (plus transversality of `ℓ` at the slab faces).  The two halves
of the design are then `SwingGeometryHolds` (P1+P2, the generic data together with the constancy of
the span between critical values) and a Morse-restricted version of this predicate, which is not yet
stated here. -/
def SwingCounting (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Prop :=
  ∀ (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
    0 < h → lam0 < lam1 → (∀ t ∈ exc, lam0 < t ∧ t < lam1) →
    (∀ lam ∈ exc, ∀ mu nu : ℝ, lam0 ≤ mu → mu < lam → lam < nu → nu ≤ lam1 →
      (∀ t ∈ exc, t < mu ∨ t = lam ∨ nu < t) →
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ mu)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ nu)) + 1 ∧
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ nu)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ mu)) + 1) ∧
    (∀ lam : ℝ, lam0 ≤ lam → lam ≤ lam1 → (∀ t ∈ exc, t ≠ lam) →
      Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ lam) = ⊥ ∨
        Work.SurgeryInvariance.WindingSpan P (sideRegion P s c σ u h ℓ lam) = ⊤)

/-- **The two halves of the design give the whole** (and hence, with the assembly
`Work.Drive.EpsFormSphere.thickHalf_of_sideSweepData`, the ε-form). -/
theorem sideSweepData_of_swingGeometry_swingCounting {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (hg : SwingGeometry P s c σ u)
    (hc : SwingCounting P s c σ u) : Nonempty (SideSweepData P s c σ u) := by
  obtain ⟨h, ℓ, lam0, lam1, exc, hpos, hlt, hexc, hstart, hfinish, hreg⟩ := hg
  obtain ⟨hjump, hdich⟩ := hc h ℓ lam0 lam1 exc hpos hlt hexc
  exact ⟨⟨h, hpos, ℓ, lam0, lam1, hlt, exc, hexc, hstart, hfinish, hreg, hjump, hdich⟩⟩


/-- **P1 + P2 at the counted configurations** (the geometry half of the design). -/
def SwingGeometryHolds : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          SwingGeometry (torusOf ψ) s c σ u

/-- **P3 + P4 at the counted configurations** (the counting half of the design). -/
def SwingCountingHolds : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          SwingCounting (torusOf ψ) s c σ u

/-- **The design from its two halves**: the geometry half (P1+P2) together with the counting half
(P3+P4) gives the residual `SideSweepExists`, and hence — with the assembly
`Work.Drive.EpsFormSphere.thickHalf_of_sideSweepData` — Pardon's ε-form. -/
theorem sideSweepExists_of_swingHolds (hg : SwingGeometryHolds) (hc : SwingCountingHolds) :
    SideSweepExists := by
  intro p q hp hq hc' ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  exact sideSweepData_of_swingGeometry_swingCounting
    (hg p q hp hq hc' ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)
    (hc p q hp hq hc' ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)

end

end Work.Drive.EpsSphere
