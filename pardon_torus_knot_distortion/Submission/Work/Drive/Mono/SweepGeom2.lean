import Mathlib
import Submission.Work.Drive.Mono.DataPackage
import Submission.Work.Drive.Mono.GoodDataPackage
import Submission.Work.Drive.Mono.AGSweep2

/-!
# The data producer of the tilted sweep in the `BoxGenE` rethreading

`Work.Drive.Mono.SweepGeomAEG` and `Work.Drive.Mono.GoodSweepGeomAEG` (`Mono/DataPackage.lean`,
`Mono/GoodDataPackage.lean`) state the geometric obligation of the tilted-sweep route at a box level
satisfying `Work.Drive.Mono.BoxGen`.  The junction route needs the *repaired* bundle
`Work.Drive.Mono.BoxGenE` (the finiteness of the vertical edge locus, and, at almost every cutting
level, `FaceCrossReg` and `FaceNoBend`), which is what the consumer of the deliverable actually
supplies (`Work.Drive.Mono.shiftGoodCentre_holds`): with only `BoxGen`, clause (c) of
`Work.Drive.Mono.JunctionGenC` is not satisfiable at a fixed centre (an arc of a vertical box edge
in the carrier, machine-checked in `Mono/NOTES_H381_edgeArc_OBSTRUCTION.md`).

This file provides the matching `BoxGenE` versions

* `Work.Drive.Mono.SweepGeomAEG2` — the producer of `Work.Drive.Mono.DataPackage` (field (D)'s
  hypotheses);
* `Work.Drive.Mono.GoodSweepGeomAEG2` — the producer of `Work.Drive.Mono.GoodDataPackage`
  (= `DataPackage ∧ GoodSweepData2`, both fields' hypotheses),

the weakening `GoodSweepGeomAEG → GoodSweepGeomAEG2` (the `BoxGenE` hypothesis is stronger than the
`BoxGen` one, so it is harmless), and the assembly of the two fields of the sweep at the *same*
datum: `GoodNoJumpInput` on `GoodDataPackage` is the per-datum field (L) of
`Work.Drive.Mono.TiltedSweepMonoAEG2`, hence of `Work.Drive.Mono.CruxCoreWdAEG2` — the residual of
the deliverable.

The per-datum no-jump is stated on `GoodDataPackage` and **not** on `DataPackage` alone: `DataPackage`
says nothing at the exceptional levels of `exc`, and two `2`-gate events at one level do drop the
span by `2` (the machine-checked `EpsForm/windingSpan_sweepRegion_eq_of_regular_REFUTED.lean`); the
event structure that excludes this is `Work.Drive.Final.GoodSweepData2`.

**SUPERSEDED — do not fire `Work.Drive.Mono.GoodNoJumpInput`.**  `GoodSweepData2` does not bound how
many events of the three types sit over one level, and — independently — `GoodDataPackage`'s level
count is restricted to `lam ∉ exc` although every event level lies in `exc`, so the (L) route has no
inessentiality exactly where it needs it.  Both holes are diagnosed in
`Submission/Work/Drive/Mono/NOTES_noJumpInput3_holds_FALSE.md` and repaired in
`Submission/Work/Drive/Mono/SweepGeom3.lean` by `Work.Drive.Mono.GoodDataPackage3` /
`Work.Drive.Mono.GoodNoJumpInput3` (which also carry `himg`, `Work.Drive.CleansDiscsWd` and the three
arithmetic binders).  The `…2` assembly below is kept only because it is a proved implication.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal

namespace Work.Drive.Mono

noncomputable section

/-- **The geometric obligation of the tilted-sweep route, `BoxGenE` form**: at every crux
configuration, at a box level in general position for the junction route, for almost every cutting
level there are tilt data satisfying the package `Work.Drive.Mono.DataPackage`. -/
def SweepGeomAEG2 (p q : ℕ) : Prop :=
  ∀ (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        BoxGenE ψ c σ s →
        ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
          ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
        ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          |u| < Submission.eps * r →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
            DataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q

/-- **The geometric obligation of the tilted-sweep route with the pinch genericity, `BoxGenE`
form**: the same as `Work.Drive.Mono.SweepGeomAEG2`, but producing the datum of the (L) route,
`Work.Drive.Mono.GoodDataPackage` (= `DataPackage ∧ GoodSweepData2`). -/
def GoodSweepGeomAEG2 (p q : ℕ) : Prop :=
  ∀ (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        BoxGenE ψ c σ s →
        ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
          ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
        ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          |u| < Submission.eps * r →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
            GoodDataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q

/-- **The `BoxGen` producer gives the `BoxGenE` one** (the extra hypothesis strengthens the
hypothesis of the producer, so it is harmless). -/
theorem sweepGeomAEG2_of_sweepGeomAEG (h : ∀ p q : ℕ, SweepGeomAEG p q) :
    ∀ p q : ℕ, SweepGeomAEG2 p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS
  exact h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG.1 hS

/-- **The `BoxGen` producer with the pinch genericity gives the `BoxGenE` one.** -/
theorem goodSweepGeomAEG2_of_goodSweepGeomAEG (h : ∀ p q : ℕ, GoodSweepGeomAEG p q) :
    ∀ p q : ℕ, GoodSweepGeomAEG2 p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS
  exact h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG.1 hS

/-- **The two fields of the sweep at the same datum, with the `BoxGenE` producer and the per-datum
no-jump on `Work.Drive.Mono.GoodDataPackage`.**  Field `(D)` is
`Work.Drive.Mono.dichotomy_of_goodDataPackage`, field `(L)` is `Work.Drive.Mono.GoodNoJumpInput`. -/
theorem tiltedSweepMonoAEG2_of_goodGeom2_and_noJump (hGeom : ∀ p q : ℕ, GoodSweepGeomAEG2 p q)
    (hNoJump : ∀ p q : ℕ, GoodNoJumpInput p q) :
    ∀ p q : ℕ, TiltedSweepMonoAEG2 p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS
  refine Filter.Eventually.mono
    (hGeom p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS) ?_
  intro u hdata hu hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hDP⟩ := hdata hu hU
  obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hDP.1.tilt
  exact ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hsize, hh, hRbox, hlow, hhigh, hl, hexc,
    dichotomy_of_goodDataPackage p q hp hq hc himg hcl (lt_trans hr hrs) hDP,
    hNoJump p q ψ K s u c σ v h R ℓ exc lam0 lam1 hDP⟩

/-- **The residual of the deliverable from the two fields.** -/
theorem cruxCoreWdAEG2_of_goodGeom2_and_noJump (hGeom : ∀ p q : ℕ, GoodSweepGeomAEG2 p q)
    (hNoJump : ∀ p q : ℕ, GoodNoJumpInput p q) : ∀ p q : ℕ, CruxCoreWdAEG2 p q :=
  cruxCoreWdAEG2_of_tiltedSweepMonoAEG2
    (tiltedSweepMonoAEG2_of_goodGeom2_and_noJump hGeom hNoJump)

end

end Work.Drive.Mono
