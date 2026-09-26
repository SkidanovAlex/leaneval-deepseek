import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.InterfacesD
import Submission.Work.BoxShrink.ledger
import Submission.Work.SurgeryInvariance.SphereSweep
import Submission.Work.BoxShrink.halving
import Submission.Work.BoxShrink.counting

/-!
# Pardon's Lemma 3 in the ε-form: the sphere-level interfaces

`Work.BoxShrink.Bubble.BubbleHalf` — Pardon's Lemma 3 conclusion with the *exact* half-region —
is **strictly stronger** than the published Lemma 3: Pardon's `doublebubble` is stated for a double
bubble *transverse* to `F` and `β`, and the form he actually applies in the proof of the theorem,
`doublebubble2` (Annals **174** (2011), §3), concludes only the perturbed statement

> `F ∩ (B(ε) + int(H_i))` has a component of genus `g` for some `i ∈ {1,2}` and every `ε > 0`.

The perturbation into general position which produces `doublebubble2` from `doublebubble` cannot be
undone (it is exactly what makes the intermediate spheres of the pinching family transverse to `F`),
so the ε-form is the statement the crux must consume.

This module supplies, for the **sphere-level route** (Pardon's *dimension* argument, i.e. the family
of spheres `{S_t}` of his Lemma 1, rather than a region-level span decomposition):

* `ThickHalf` — the ε-form conclusion at one box/plane configuration: an essential loop of the
  surface within Euclidean distance `ε` of one of the two half-regions;
* `PinchEps` — the residual of the route: **Pardon's pinching family exists, ending at a double
  bubble whose two halves are arbitrarily close to the two half-regions** (`SphereSweep` records the
  family with Pardon's local models: isolated `2`-surgeries and ambient isotopies in between);
* `CountingHalfEpsSphere` — the ε-form for the crux configurations, in the exact shape of
  `Work.Drive.CountingHalfW` (same hypotheses), and the proof
  `countingHalfEpsSphere_of_pinchEps` that the residual implies it, through the *already proved*
  double-bubble theorem `Work.SurgeryInvariance.SphereSweep.double_bubble` (the dimension argument:
  the winding span is constant along a `SphereSweep`);
* the geometric conversion `hasEssBox_of_thickHalf`: an essential loop within `ε` of a half-region
  fits in Pardon's box of size `shrinkFactor * r`, which is where the ε-margin of the crux
  (`s < (1+eps) * r`, `|u| < eps * r`, *strict*) is spent.
-/

/-
## The route to the residual (for a prover of `PinchEps` / the ε-form)

The workspace already contains every ingredient of Pardon's proof *except* the family itself; the
following decomposition is the one this file is designed around.

1. **The family.**  Pardon's spheres `S_t` are the boundary spheres of his `2`-surgery family along
   the flat disc `D = cutDisc s c σ u`: `S_0 = ∂PBox s c σ`, and at the pinching parameter the neck
   closes and the sphere splits into the two half-spheres of the double bubble.  The one structural
   fact his counting uses is that **every intermediate sphere lies over the footprint**
   `footprint s c σ u = sphereSet c σ s ∪ cutDisc s c σ u` (`Work.Step2.footprint`): `S_t` is the
   boundary sphere of the box with a *dimple* pushed along `D`, so `S_t ⊆ footprint` — whence
   `S_t ∩ F ⊆ (box-sphere trace) ∪ (cut-disc trace)`.
2. **The two endpoint traces are inessential.**  The box-sphere trace carries no essential loop from
   the sphere count (`Work.BoxShrink.not_containsEssentialLoop_of_sliced`, using the crux's
   `SlicedSphere` and `Work.Drive.CleansDiscsW`); the cut-disc trace carries none from the plane
   count (`Work.Smooth.Plane.windingSpan_eq_bot_of_cleansInConvexPlane`, the planar innermost-disc
   argument, plus `Work.BoxBubble.encard_range_inter_le_param` to pass from parameters to points).
   Hence, by (1), **every** intermediate trace is inessential — no `mustbeinessential` at the
   intermediate spheres is needed, only the two endpoints.
3. **The local models.**  An inessential simple closed curve of `F` inside a sphere bounds a disc of
   `F`, and the trace of a sphere in general position splits it into such discs: the passage between
   two consecutive intermediate regions is the addition/removal of the interior of an embedded disc
   of `F` (`Work.SurgeryInvariance.SurgeryShapeRaw`), or nothing (`RegionIsotopic`).  This is where
   the `SphereSweep` structure of the statement is used; the dimension argument is then
   `Work.SurgeryInvariance.Sweep.windingSpan_eq` (the span is constant along a `Sweep`), and the
   double-bubble conclusion is `Work.SurgeryInvariance.SphereSweep.double_bubble`
   (see `countingHalfEpsSphere_of_pinchEps`).
4. **The ε-endpoint.**  At the pinching parameter the sphere is not transverse to `F`, which is why
   Pardon perturbs the double bubble into general position (`doublebubble2`).  The perturbation may
   be taken arbitrarily small, which is exactly the two `ε`-clauses of `PinchEps`; at fixed `ε > 0`
   the perturbed halves may be assumed in general position, and by (2)+(3) the perturbed family is a
   `SphereSweep`.  In the workspace the `ε`-clause is what replaces the missing perturbation
   machinery: it is the *assertion* that a family ending that close to the original double bubble
   exists.

Comments, in particular about the two traps of `HANDOFF.md`:

* the *explicit* family of `Work.Step2` (`pinchRegion`, the box with an expanding flat slab removed)
  does **not** have the local model: its changed piece at the pinching parameter is the trace of a
  closed band (the slice), which is not open in the surface
  (`Work.Step2.not_isOpenInCarrier_neckPiece_of_accumulating`), so it cannot be used as the sweep;
* the *uncounted* forms are false (`Work.BoxShrink.PinchOff.RefuteDrop.not_dropCase`,
  `Work.BoxShrink.PinchOff.not_bubbleHalf_tangent`): the counting at the endpoints is essential, and
  no statement of general position alone may be substituted for it.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal
open Metric

namespace Work.Drive.EpsSphere

noncomputable section

abbrev torusOf (ψ : Submission.Diffeo) : Work.CoreTopology.ParamTorus :=
  Work.Smooth.Morse.torus ψ

/-- **The ε-form at one box/plane configuration**: an essential loop of the surface within
Euclidean distance `ε` of the upper half-region, or one within `ε` of the lower half-region. -/
def ThickHalf (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u ε : ℝ) : Prop :=
  (∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, γ t ∈ thickening ε (Work.BoxShrink.Core.upperRegion P s c σ u)) ∨
    (∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, γ t ∈ thickening ε (Work.BoxShrink.Core.lowerRegion P s c σ u))

/- **WARNING: this residual is refuted / abandoned (do not use it).**

A colleague's audit (`Work.Drive.EpsFormSphere.pinchEps`, declared FALSE, with the machine-checked
derivation reproduced below) shows that the endpoint clauses of this statement imply the *strictly
stronger* conclusion

  `W(boxRegion) ≤ W(thick ε upperRegion) ⊔ W(thick ε lowerRegion)`,

for every configuration of the hypotheses: the winding span is constant along a `SphereSweep`
(`Work.SurgeryInvariance.Sweep.windingSpan_eq`), the final region is the union of the three disjoint
open pieces `H₁`, `H₂`, `D.interior`, and `D.interior` is inessential
(`Work.SurgeryInvariance.DiscRegion.windingSpan_interior_eq_bot`), so the span of the *whole* region
inside the box is bounded by the two thickened halves — whereas Pardon's ε-form only asks for *one
loop* near a half.  The statement is therefore not the ε-form of Pardon's `doublebubble2` and must
not be used as a residual; the ε-form `CountingHalfEpsSphere` (and its shifted form) is the honest
target.

There is a second, structural reason not to build on `SphereSweep` here: a single `2`-surgery of the
library (`SurgeryShape`/`SurgeryShapeRaw`) removes or adds a piece which is *clopen* in the region
(`Work.BoxShrink.Pinch.Warning.surgeryStepSmall_grow_or_empty`,
`Work.BoxShrink.Bubble.Obstruction.surgeryStepZero_eq_self_or_empty`), so a preconnected region
cannot be shrunk by one — while Pardon's pinch shrinks the box region to the two halves through a
neck whose trace is *not* clopen.  The pinch is therefore only modelable with the degenerate step
kept as an explicit endgame hypothesis (`Work.BoxShrink.Pinch.PinchFamily`), or after the
perturbation of `doublebubble2`, which is itself part of the residual.

The statement below is kept only for the record (and because the implication
`countingHalfEpsSphere_of_pinchEps` is still a theorem). -/
/-- **The residual of the sphere-level route: Pardon's pinching family, with the endpoint within
`ε` of the two half-regions.**

At every configuration carrying the counting data of the crux, and for every `ε > 0`, there is a
one-parameter family of embedded spheres (`Work.SurgeryInvariance.SphereSweep`: ambient isotopies of
`ℝ³` preserving the surface between the finitely many exceptional parameters, a single `2`-surgery
at each of them) which starts at the boundary sphere of Pardon's box — so `region 0` is the region
`F ∩ int(S_0)` of the challenge — and ends at the perturbed double bubble: the two open pieces
`H₁`, `H₂` of the surface cut out by the perturbed halves, together with the trace of the perturbed
pinching disc; and each `H_i` is within distance `ε` of the corresponding half-region.

This is Pardon's `doublebubble2` in the sphere vocabulary: the family is his `2`-surgery family
along the cutting disc (whose counting he performs at the intermediate spheres, so that the *only*
local models which occur are the two of `SphereSweep`), and the perturbation into general position
is what produces the two `ε`-neighbourhood clauses. -/
def PinchEps : Prop :=
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
          ∀ ε : ℝ, 0 < ε →
            ∃ (S : Work.SurgeryInvariance.SphereSweep (torusOf ψ))
              (H₁ H₂ : Set R3) (D : Work.SurgeryInvariance.DiscRegion (torusOf ψ)),
              Work.SurgeryInvariance.IsOpenInCarrier (torusOf ψ) H₁ ∧
              Work.SurgeryInvariance.IsOpenInCarrier (torusOf ψ) H₂ ∧
              Disjoint H₁ H₂ ∧ Disjoint (H₁ ∪ H₂) D.interior ∧
              S.region 0 = Work.BoxShrink.Core.boxRegion (torusOf ψ) s c σ ∧
              S.region 1 = (H₁ ∪ H₂) ∪ D.interior ∧
              ((H₁ ⊆ thickening ε
                    (Work.BoxShrink.Core.upperRegion (torusOf ψ) s c σ u) ∧
                H₂ ⊆ thickening ε
                    (Work.BoxShrink.Core.lowerRegion (torusOf ψ) s c σ u)) ∨
               (H₁ ⊆ thickening ε
                    (Work.BoxShrink.Core.lowerRegion (torusOf ψ) s c σ u) ∧
                H₂ ⊆ thickening ε
                    (Work.BoxShrink.Core.upperRegion (torusOf ψ) s c σ u)))

/-- **Pardon's ε-form for the crux configurations** (same hypotheses as `Work.Drive.CountingHalfW`,
weakened conclusion). -/
def CountingHalfEpsSphere : Prop :=
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
          ∀ ε : ℝ, 0 < ε → ThickHalf (torusOf ψ) s c σ u ε

/-- **The residual gives the ε-form**, through the double-bubble theorem of the sphere vocabulary:
the winding span is constant along a `SphereSweep`, the initial region of the family is the region
inside the box (essential, by `HasEssBox`), and the final region is the union of the two perturbed
halves with the trace of the pinching disc, so one of the two perturbed halves carries the essential
loop — and each of them lies within `ε` of a half-region. -/
theorem countingHalfEpsSphere_of_pinchEps (h : PinchEps) : CountingHalfEpsSphere := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  obtain ⟨S, H₁, H₂, D, hopen₁, hopen₂, hdisj, hdisjZ, hzero, hone, hεhalf⟩ :=
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU ε hε
  have h0 : (torusOf ψ).ContainsEssentialLoop (S.region 0) := by
    rw [hzero]
    exact Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (le_of_lt hrs) hbox
  have hcases := Work.SurgeryInvariance.SphereSweep.double_bubble S hopen₁ hopen₂ hdisj hdisjZ
    hone h0
  rcases hcases with ⟨γ, hess, hmem⟩ | ⟨γ, hess, hmem⟩
  · rcases hεhalf with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl ⟨γ, hess, fun t => h1 (hmem t)⟩
    · exact Or.inr ⟨γ, hess, fun t => h1 (hmem t)⟩
  · rcases hεhalf with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact Or.inr ⟨γ, hess, fun t => h2 (hmem t)⟩
    · exact Or.inl ⟨γ, hess, fun t => h2 (hmem t)⟩


/-- **The *shifted* ε-form**: for every `ε > 0`, an essential loop of the surface in the box of size
`s + ε` lying strictly above the plane shifted down by `ε` (the upper branch), or strictly below the
plane shifted up by `ε` (the lower branch).

This is the weakest of the ε-forms: Pardon's `doublebubble2` conclusion (a loop within distance `ε`
of a *half-box*) and the ε-form `ThickHalf` both imply it, and it is exactly what the halving
geometry of `Work.BoxShrink.halving` consumes (`Work.Drive.EpsSphere.hasEssBox_of_thickHalfShifted`),
because a point within `ε` of the half-region `{y (σ 2) > c (σ 2) + u}` is in `PBox (s + ε) c σ` and
above the plane shifted down by `ε`. -/
def ThickHalfShifted (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u ε : ℝ) : Prop :=
  (∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, γ t ∈ Submission.PBox (s + ε) c σ ∧ c (σ 2) + u - ε < γ t (σ 2)) ∨
    (∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
      ∀ t : ℝ, γ t ∈ Submission.PBox (s + ε) c σ ∧ γ t (σ 2) < c (σ 2) + u + ε)

/-- **The shifted ε-form for the crux configurations** (same hypotheses as the ε-form
`CountingHalfEpsSphere`, conclusion weakened to `ThickHalfShifted`). -/
def CountingHalfEpsShifted : Prop :=
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
          ∀ ε : ℝ, 0 < ε → ThickHalfShifted (torusOf ψ) s c σ u ε

end

end Work.Drive.EpsSphere
