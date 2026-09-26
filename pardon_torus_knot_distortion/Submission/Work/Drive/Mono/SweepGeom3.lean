import Mathlib
import Submission.Work.Drive.Mono.SweepGeom2
import Submission.Work.Drive.Final.AnyEventDefs

/-!
# The third data package: `GoodSweepData3` with the two fields of the sweep

Project lead, `Submission/Work/Drive/Final/NOTES_LEAD_L4_L1.md` §2 and §4: the bundle that the (L)
route actually needs is `Work.Drive.Final.GoodSweepData3` (the event structure of the three types,
`EdgeFree`, the universal `SlabBoxCrossReg`, `GammaTransverse`, `FaceRegClosed`, the corner direction,
`offK` for all three types, *one event per level*, and the sphere cover `SphereCoverAt` at every level
of the window), not the drifted `GoodSweepData2`.

This module fixes the vocabulary of the resulting obligations and the assembly:

* `Work.Drive.Mono.GoodDataPackage3` — `Work.Drive.Mono.DataPackage ∧ GoodSweepData3`, the datum at
  which both fields of the sweep are analysed;
* `Work.Drive.Mono.GoodNoJumpInput3` — field (L) at such a datum (the *honest* per-datum no-jump:
  at an event level it is H330's `noJumpBelowAt_of_anyEvent`, elsewhere the trace-curve argument);
* `Work.Drive.Mono.GoodSweepGeomAEG3` — the `BoxGenE` producer of such a datum;
* the assembly `Work.Drive.Mono.cruxCoreWdAEG2_of_goodGeom3_and_noJump`, which is the residual
  `Work.Drive.Mono.CruxCoreWdAEG2` of the deliverable.

Why the third bundle and not the second: `GoodSweepData2` does not say how many events of the three
types lie over one level, and two `2`-gate events at one level *do* drop the span by `2`
(machine-checked: `Submission/Work/Drive/EpsForm/windingSpan_sweepRegion_eq_of_regular_REFUTED.lean`);
the clause "one event per level" of `GoodSweepData3` is exactly what excludes that.  This is the
finding that made `Work.Drive.Mono.noJumpInput_holds` (on `GoodDataPackage`) FALSE — see
`Submission/Work/Drive/Final/NOTES_H381_to_H330_GoodNoJumpInput_FALSE.md`.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal

namespace Work.Drive.Mono

noncomputable section

/-- **The third data package**: `Work.Drive.Mono.DataPackage` (field (D)) together with
`Work.Drive.Final.GoodSweepData3` (the event structure of the three types and the pinch genericity
of field (L)), **and** the level count at *every* level of the window.

The last conjunct is not redundant with `DataPackage.count`, which is restricted to `lam ∉ exc`:
every event level lies in `exc`, and the (L) route needs the trace's *inessentiality* exactly at those
levels (Pardon's counting is what produces it).  This is the repair diagnosed by the prover of
`Work.Drive.Mono.noJumpInput3_holds`
(`Submission/Work/Drive/Mono/NOTES_noJumpInput3_holds_FALSE.md` §1–§5); the unrestricted count is
`Work.Drive.Mono.levelCount_lt_min_all`, produced from the same non-grazing package the producer
already establishes. -/
def GoodDataPackage3 (ψ : Submission.Diffeo) (K : Knot) (s u : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ)
    (lam0 lam1 : ℝ) (p q : ℕ) : Prop :=
  DataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q ∧
  Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1 ∧
  (∀ lam ∈ Set.Icc lam0 lam1,
      Set.encard (Set.range K.curve ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞))

/-- **The third data package gives the second** (`GoodSweepData3 → GoodSweepData2`). -/
theorem goodDataPackage_of_goodDataPackage3 {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {hh RR : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} {p q : ℕ}
    (hDP : GoodDataPackage3 ψ K s u c σ v hh RR ℓ exc lam0 lam1 p q) :
    GoodDataPackage ψ K s u c σ v hh RR ℓ exc lam0 lam1 p q :=
  ⟨hDP.1, hDP.2.1.1⟩

/-- **Field (L) as a per-datum obligation at a `GoodDataPackage3` datum.**  This is
`Work.Drive.Mono.GoodNoJumpInput` with the honest hypothesis bundle
(`GoodSweepData3` in place of `GoodSweepData2`). -/
def GoodNoJumpInput3 (p q : ℕ) : Prop :=
  ∀ (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot),
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
  ∀ (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ)
    (d : ℝ) (_hd : 0 ≤ d) (_hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (_hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
          ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))),
    GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q →
    ∀ lam ∈ Set.Icc lam0 lam1,
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥ →
      ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
        Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) ≠ ⊤

/-- **The geometric obligation of the tilted-sweep route with the third bundle**: at every crux
configuration, at a box level in general position for the junction route, for almost every cutting
level there are tilt data satisfying `Work.Drive.Mono.GoodDataPackage3`. -/
def GoodSweepGeomAEG3 (p q : ℕ) : Prop :=
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
            GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q

/-- **The third producer gives the second** (`GoodSweepData3 → GoodSweepData2`). -/
theorem goodSweepGeomAEG2_of_goodSweepGeomAEG3 (h : ∀ p q : ℕ, GoodSweepGeomAEG3 p q) :
    ∀ p q : ℕ, GoodSweepGeomAEG2 p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS
  refine Filter.Eventually.mono
    (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS) ?_
  intro u hdata hu hU
  obtain ⟨v, h', R, ℓ, lam0, lam1, exc, hDP⟩ := hdata hu hU
  exact ⟨v, h', R, ℓ, lam0, lam1, exc, goodDataPackage_of_goodDataPackage3 hDP⟩

/-- **The two fields of the sweep at the same datum, with the third bundle.** -/
theorem tiltedSweepMonoAEG2_of_goodGeom3_and_noJump (hGeom : ∀ p q : ℕ, GoodSweepGeomAEG3 p q)
    (hNoJump : ∀ p q : ℕ, GoodNoJumpInput3 p q) :
    ∀ p q : ℕ, TiltedSweepMonoAEG2 p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS
  refine Filter.Eventually.mono
    (hGeom p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS) ?_
  intro u hdata hu hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hDP⟩ := hdata hu hU
  have hDP2 : GoodDataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q :=
    goodDataPackage_of_goodDataPackage3 hDP
  obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hDP2.1.tilt
  exact ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hsize, hh, hRbox, hlow, hhigh, hl, hexc,
    dichotomy_of_goodDataPackage p q hp hq hc himg hcl (lt_trans hr hrs) hDP2,
    hNoJump p q hp hq hc ψ K himg hcl s u c σ v h R ℓ exc lam0 lam1 d hd hsmall hS hDP⟩

/-- **The residual of the deliverable from the third bundle's two fields.** -/
theorem cruxCoreWdAEG2_of_goodGeom3_and_noJump (hGeom : ∀ p q : ℕ, GoodSweepGeomAEG3 p q)
    (hNoJump : ∀ p q : ℕ, GoodNoJumpInput3 p q) : ∀ p q : ℕ, CruxCoreWdAEG2 p q :=
  cruxCoreWdAEG2_of_tiltedSweepMonoAEG2
    (tiltedSweepMonoAEG2_of_goodGeom3_and_noJump hGeom hNoJump)

end

end Work.Drive.Mono
