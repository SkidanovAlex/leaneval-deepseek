import Mathlib
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.ae_cutTransverse
import Submission.Work.Drive.Mono.ae_noCritValue_near
import Submission.Work.Drive.Mono.ae_exists_goodV
import Submission.Work.Drive.Mono.NoBend
import Submission.Work.Drive.Mono.g3_vertEdge_margin_ae
import Submission.Work.Drive.Mono.knot_deriv_of_sweepHeight_crit
import Submission.Work.Drive.Final.sweep_mono
import Submission.Work.Drive.Mono.geom3Extra
import Submission.Work.Drive.Mono.ae_slabBoxCrossReg
import Submission.Work.Drive.Mono.g3OneEvDefs

/-!
# The almost-everywhere wrapper of `Work.Drive.Mono.geom3Data_exists`

`Work.Drive.Mono.geom3Data_exists : Work.Drive.Mono.Geom3DataExists` (the fixed target) is a
`∀ᵐ u` statement: at almost every cutting level `u` the crux hypotheses in force, there are tilt
data satisfying `Work.Drive.Mono.Geom3Data`.  This file isolates the *bookkeeping* half of that:
the pointwise facts that the fleet's a.e.-producers deliver at `u` are bundled into the predicate
`Work.Drive.Mono.G3Pointwise`, the bundle is shown to hold for almost every `u` (from
`BoxGenE`, `ae_cutTransverse`, `ae_noCritValue_near`, `ae_exists_goodV_near`, `ae_noBendCrossing`
and `g3_vertEdge_margin_ae`), and `Geom3DataExists` is reduced to the single-level producer
`hAtU`.

The remaining content of the target is therefore exactly the single-level producer
`Work.Drive.Mono.geom3DataAtU_exists` (`Submission/Work/Drive/Mono/geom3DataAtU_exists.lean`).

## Why these six facts and no others

* `Work.Drive.Mono.CutTransverse` — needed for the level count and for the trace arcs;
* `∃ δg` — the *flat* no-grazing margin of the knot, the input of the merged witness's
  `hnograz`;
* `Work.Drive.Mono.FaceCrossReg ∧ Work.Drive.Mono.FaceNoBend` — the trace-arc hypotheses of
  `Work.Drive.Mono.gammaArcs_exist` and `Work.Drive.Mono.gammaArc_noBend`; they are a conjunct of
  `Work.Drive.Mono.BoxGenE`, so no separate producer is needed;
* the *uniform* form of the no-grazing margin (`Work.Drive.Mono.ae_exists_goodV_near`, with
  threshold `θ = 1/16`, strictly stronger than the `εg`/`δg` pair the witness consumes: it bounds
  the margin by the *same* number that bounds the distance to `shiftVσ σ 1`);
* the knot no-bend clause at a vertical-tangent box-boundary crossing
  (`Work.Drive.Mono.ae_noBendCrossing`);
* the vertical-edge margin `∃ mE` (`Work.Drive.Mono.g3_vertEdge_margin_ae`), which supplies the
  uniform lower bound of `Work.Drive.Mono.EdgeFree` through
  `Work.Drive.Mono.g3_edgeFree_of_margin`.

The list is *closed under what the producer can use*: every other a.e.-`u` statement of the
fleet (`ae_faceCrossReg_of_boxGen`, `knotCritLevels_null`, `no_eventOnFace_null`,
`faceEvent_degen_null`, `ae_slabBoxCrossReg`, `g3_offKFace_bad_null`, `g3_corner_event_bad_null`)
gives a *null set of forbidden parameters* `(h, τ)` or `h`, which the producer consumes through the
`S`-avoidance of `Work.Drive.Mono.tiltData_window_of_dir_export_param`, not as a pointwise fact.
-/

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal

namespace Work.Drive.Mono

set_option maxHeartbeats 1000000

noncomputable section

/-- **The pointwise facts available at a good cutting level `u`.**  This is the bundle that
`Work.Drive.Mono.g3_ae_pointwise` produces for almost every `u` from the crux hypotheses; the
single-level producer `Work.Drive.Mono.geom3DataAtU_exists` consumes it. -/
def G3Pointwise (ψ : Submission.Diffeo) (K : Knot) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Prop :=
  Work.Drive.Mono.CutTransverse K s c σ u ∧
  (∃ δg : ℝ, 0 < δg ∧ ∀ t : ℝ,
      deriv (fun r : ℝ => (K.curve r) (σ 2)) t = 0 →
      δg ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)|) ∧
  Work.Drive.Mono.FaceCrossReg ψ c σ s u ∧
  Work.Drive.Mono.FaceNoBend ψ c σ s u ∧
  (∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ ε ≤ 1 / 16 ∧ δ ≤ 1 / 16 ∧
    ∀ v : R3, ‖v‖ = 1 → ‖v - Work.BoxShrink.shiftVσ σ 1‖ < ε →
      ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
        δ ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
  (∀ t : ℝ, K.curve t ∈ closure (Submission.PBox s c σ) →
      (K.curve t) (σ 2) = c (σ 2) + u →
      Work.Drive.Mono.vertVel K (Work.BoxShrink.shiftVσ σ 1) t = 0 →
      Work.Drive.Mono.vertAcc K (Work.BoxShrink.shiftVσ σ 1) t = 0) ∧
  (∃ mE : ℝ, 0 < mE ∧ ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
      |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
      mE ≤ |z (σ 2) - (c (σ 2) + u)|) ∧
  G3OneEv ψ s u c σ

/-- **The one-event slice nullity is a conjunct of `Work.Drive.Mono.G3Pointwise`.** -/
theorem g3Pointwise_oneEv {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} (hP : G3Pointwise ψ K s u c σ) : G3OneEv ψ s u c σ :=
  hP.2.2.2.2.2.2.2

/-- **The vertical-edge margin is a conjunct of `Work.Drive.Mono.G3Pointwise`.** -/
theorem g3Pointwise_mE {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} (hP : G3Pointwise ψ K s u c σ) :
    ∃ mE : ℝ, 0 < mE ∧ ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
      |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
      mE ≤ |z (σ 2) - (c (σ 2) + u)| :=
  hP.2.2.2.2.2.2.1

/-- **The knot's box-sphere trace is finite**, from the crux count `hS`. -/
theorem g3_boxSphereTrace_finite (K : Knot) {s : ℝ} (c : R3) (σ : Equiv.Perm (Fin 3)) {d : ℝ}
    (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))) :
    ({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}).Finite := by
  have h1 : ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hne : ((↑({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) = s}.encard) : ENNReal)) ≠ ⊤ :=
    fun hh => h1 (top_le_iff.mp (hh ▸ hS))
  exact Set.encard_lt_top_iff.mp (ENat.toENNReal_lt_top.mp (lt_top_iff_ne_top.mpr hne))

/-- **The pointwise facts hold at almost every cutting level.** -/
theorem g3_ae_pointwise (ψ : Submission.Diffeo) (K : Knot) {r s : ℝ}
    (hr : 0 < r) (hrs : r < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hBG : Work.Drive.Mono.BoxGenE ψ c σ s)
    (hfin : ({t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}).Finite)
    (hOneEv : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), G3OneEv ψ s u c σ) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      G3Pointwise ψ K s u c σ := by
  have hs : 0 < s := lt_trans hr hrs
  have hcut_ae : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Drive.Mono.CutTransverse K s c σ u :=
    ae_cutTransverse K hs c σ hfin
  have hδ_ae : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, deriv (fun r : ℝ => (K.curve r) (σ 2)) t = 0 →
        δ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)| :=
    ae_noCritValue_near K c σ
  have hV_ae : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ (ε δ : ℝ), 0 < ε ∧ 0 < δ ∧ ε ≤ 1 / 16 ∧ δ ≤ 1 / 16 ∧
        ∀ v : R3, ‖v‖ = 1 → ‖v - Work.BoxShrink.shiftVσ σ 1‖ < ε →
          ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
            deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
            δ ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)| :=
    ae_exists_goodV_near K hs c σ (θ := 1 / 16) (by norm_num)
  have hnb_ae : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ t : ℝ, K.curve t ∈ closure (Submission.PBox s c σ) →
        (K.curve t) (σ 2) = c (σ 2) + u →
        Work.Drive.Mono.vertVel K (Work.BoxShrink.shiftVσ σ 1) t = 0 →
        Work.Drive.Mono.vertAcc K (Work.BoxShrink.shiftVσ σ 1) t = 0 :=
    ae_noBendCrossing K (Work.BoxShrink.shiftVσ σ 1) c σ s
  have hmE_ae : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∃ mE : ℝ, 0 < mE ∧ ∀ z : R3,
        z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
        |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
        mE ≤ |z (σ 2) - (c (σ 2) + u)| :=
    g3_vertEdge_margin_ae ψ hBG.2.1
  filter_upwards [hcut_ae, hδ_ae, hBG.2.2, hV_ae, hnb_ae, hmE_ae, hOneEv]
    with u hcut hδ hFCB hV hnb hmE honeEv
  exact ⟨hcut, hδ, hFCB.1, hFCB.2, hV, hnb, hmE, honeEv⟩

/-- **The target reduces to the single-level producer.**  If at every cutting level `u` carrying the
pointwise facts `Work.Drive.Mono.G3Pointwise` one can produce `Work.Drive.Mono.Geom3Data`, then
`Work.Drive.Mono.Geom3DataExists` holds. -/
theorem geom3Data_exists_of_atU
    (hOneEv : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
      ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), G3OneEv ψ s u c σ)
    (hAtU : ∀ (ψ : Submission.Diffeo) (K : Knot) {r s u : ℝ}
      (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
      (hu : |u| < Submission.eps * r)
      (c : R3) (σ : Equiv.Perm (Fin 3)) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
      (d : ℝ) (hd : 0 ≤ d) (hbound : Work.Sweep.IsDistortionBound K d)
      (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
      (hbox : Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ)
      (hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
          {y : R3 | Submission.boxNorm c σ y = s})
      (hBG : Work.Drive.Mono.BoxGenE ψ c σ s)
      (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
        ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
      (hsub : Set.range K.curve ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier)
      (hU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          K.curve t ∈ Submission.PBox s c σ ∧
          (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
        ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)))
      (hP : Work.Drive.Mono.G3Pointwise ψ K s u c σ),
      ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
        Work.Drive.Mono.Geom3Data ψ K s u c σ v h R ℓ exc lam0 lam1 p q) :
    Work.Drive.Mono.Geom3DataExists := by
  intro ψ K r s hr hrs hs c σ p q hp hq d hd hbound hsmall hbox hslice hBG hS hsub
  have hs' : 0 < s := lt_trans hr hrs
  have hfin := g3_boxSphereTrace_finite K c σ hS
  filter_upwards [g3_ae_pointwise ψ K hr hrs c σ hBG hfin (hOneEv ψ s c σ)] with u hP
  intro hu hU
  exact hAtU ψ K hr hrs hs hu c σ p q hp hq d hd hbound hsmall hbox hslice hBG hS hsub hU hP

/-! ## Two glue lemmas for the single-level producer

Both are consumed by `Work.Drive.Mono.geom3DataAtU_exists`; they are pure bookkeeping that does not
belong to any single mathematical input. -/

/-- **`offK` for the `IsEvent` branch** (and hence `Geom2Data`'s conjunct 18, `G3Extra`'s `offK`
on the `IsEvent` branch, and the `IsEvent` branch of the one-event clause): if the knot's ℓ-value
has non-vanishing derivative everywhere in the closed slab inside the box, then no critical point of
the sweep height in the closed slab inside the box lies on the knot.

The proof is the contrapositive: `K.curve t = par ψ p` with `p` critical gives
`deriv (ℓ ∘ K.curve) t = 0` by `Work.Drive.Mono.knot_deriv_of_sweepHeight_crit` (which uses exactly
the hypothesis `hsub : Set.range K.curve ⊆ carrier` carried by `Work.Drive.Mono.Geom3DataExists`),
contradicting the ℓ-transversality at the knot. -/
theorem g3_offK_isEvent {ψ : Submission.Diffeo} {K : Knot} {s u h : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    (hsub : Set.range K.curve ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hwall : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u v (K.curve t)| ≤ h →
      deriv (fun r : ℝ => ℓ (K.curve r)) t ≠ 0) :
    ∀ p : ℝ × ℝ, Work.Drive.Final.IsEvent ψ s c σ u v h ℓ p →
      ∀ t : ℝ, K.curve t ≠ Work.BoxShrink.Pinch.par ψ p := by
  intro p hp t hcon
  refine (hwall t ?_ ?_) (Work.Drive.Mono.knot_deriv_of_sweepHeight_crit ψ K ℓ hsub hcon hp.2.2)
  · rw [hcon]; exact hp.1
  · rw [hcon]
    simpa [Work.Drive.Final.slabFn_apply, Work.Drive.EpsForm.tiltedSlabClosed] using hp.2.1

/-- **`Geom2Data`'s `offK` from the knot ℓ-transversality**: the `p`-form of
`Work.Drive.Mono.g3_offK_isEvent`. -/
theorem g3_offK_of_hwall {ψ : Submission.Diffeo} {K : Knot} {s u h : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    (hsub : Set.range K.curve ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hwall : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u v (K.curve t)| ≤ h →
      deriv (fun r : ℝ => ℓ (K.curve r)) t ≠ 0) :
    ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p ∈
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p = 0 →
      ∀ t : ℝ, K.curve t ≠ Work.BoxShrink.Pinch.par ψ p := by
  intro p hpbox hslab hcrit t hcon
  refine (hwall t ?_ ?_) (Work.Drive.Mono.knot_deriv_of_sweepHeight_crit ψ K ℓ hsub hcon hcrit)
  · rw [hcon]; exact hpbox
  · rw [hcon]
    simpa [Work.Drive.Final.slabFn_apply, Work.Drive.EpsForm.tiltedSlabClosed] using hslab

/-- **The one-event-per-level clause from `TiltedGenericity` (iv) plus the absence of bad pairs.**
The `{IsEvent, IsEvent}` pairs are excluded by clause (iv) at the datum; every pair with at least one
member a face or corner event is excluded by the hypothesis `hno`, which the producer obtains from the
null set of `Work.Drive.Mono.g3_oneEvent_bad_null_nochord` (through
`Work.Drive.Mono.tiltData_window_of_dir_export_param`). -/
theorem g3_oneEvent_clause {ψ : Submission.Diffeo} {s u h : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    (hgen : Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc)
    (hno : ¬ ∃ p p' : ℝ × ℝ,
      Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p ∧
      Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p' ∧
      ¬ (Work.Drive.Final.IsEvent ψ s c σ u v h ℓ p ∧
         Work.Drive.Final.IsEvent ψ s c σ u v h ℓ p') ∧
      ℓ (Work.BoxShrink.Pinch.par ψ p) = ℓ (Work.BoxShrink.Pinch.par ψ p') ∧
      Work.BoxShrink.Pinch.par ψ p ≠ Work.BoxShrink.Pinch.par ψ p') :
    ∀ p p' : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p →
      Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p' →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = ℓ (Work.BoxShrink.Pinch.par ψ p') →
      Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p' := by
  intro p p' hp hp' hℓ
  by_cases hboth : Work.Drive.Final.IsEvent ψ s c σ u v h ℓ p ∧
      Work.Drive.Final.IsEvent ψ s c σ u v h ℓ p'
  · exact hgen.2.2.2 p p' hboth.1.1 hboth.2.1 hboth.1.2.1 hboth.2.2.1
      hboth.1.2.2 hboth.2.2.2 hℓ
  · by_contra hne
    exact hno ⟨p, p', hp, hp', hboth, hℓ, hne⟩

/-! ## The vanishing-coordinate structure of the box-sphere trace

This is the *elementary* substitute for the countability of the directions of the straight
subsegments of the trace (`Work.Drive.Mono.g3_trace_segdir_countable`), and the route by which the
producers of the fleet actually get the no-chord hypothesis `hnc` of
`Work.Drive.Mono.g3_oneEvent_bad_null_nochord`: along a segment on which `boxNorm c σ ·` is
constant and equal to `s`, some coordinate is constant, so **the direction of every straight
subsegment of the trace has a vanishing coordinate**.  Consequently any direction `v` with *no*
vanishing coordinate is not the direction of such a subsegment. -/

/-- **A chord of the box sphere has a constant coordinate.**  If `boxNorm c σ · = s` at both ends
`y, y'` and at the midpoint, then some coordinate of `y` equals the corresponding coordinate of
`y'`.  (Convexity of the coordinates: the midpoint attains the maximum defining the box norm, so
the corresponding coordinate term is extremal at both ends; and the terms cannot be extremal with
opposite signs, since then the midpoint's term would vanish.) -/
theorem g3_chord_coord_eq (c : R3) (σ : Equiv.Perm (Fin 3)) {s : ℝ}
    {y y' : R3} (hy : Submission.boxNorm c σ y = s) (hy' : Submission.boxNorm c σ y' = s)
    (hm : Submission.boxNorm c σ ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y') = s) :
    ∃ k : Fin 3, y (σ k) = y' (σ k) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : Fin 3,
      |((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y') (σ k) - c (σ k)| / Submission.boxSide k = s := by
    have h := hm
    rw [Submission.boxNorm] at h
    rw [max_eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h2, _⟩
    · rw [max_eq_iff] at h1
      rcases h1 with ⟨h0, _⟩ | ⟨h1', _⟩
      · exact ⟨0, h0⟩
      · exact ⟨1, h1'⟩
    · exact ⟨2, h2⟩
  have hbk : 0 < Submission.boxSide k := Submission.boxSide_pos k
  have hmk : |((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y') (σ k) - c (σ k)|
      = Submission.boxSide k * s := by
    rw [div_eq_iff (ne_of_gt hbk)] at hk
    linarith [hk]
  have hmcoord : ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y') (σ k) - c (σ k)
      = ((y (σ k) - c (σ k)) + (y' (σ k) - c (σ k))) / 2 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hyle : |y (σ k) - c (σ k)| ≤ Submission.boxSide k * s := by
    have h1 := g3_boxNorm_coord_le c σ y k
    rw [hy] at h1
    rw [div_le_iff₀ hbk] at h1
    linarith [h1]
  have hy'le : |y' (σ k) - c (σ k)| ≤ Submission.boxSide k * s := by
    have h1 := g3_boxNorm_coord_le c σ y' k
    rw [hy'] at h1
    rw [div_le_iff₀ hbk] at h1
    linarith [h1]
  have htri : |(y (σ k) - c (σ k)) + (y' (σ k) - c (σ k))|
      ≤ |y (σ k) - c (σ k)| + |y' (σ k) - c (σ k)| := abs_add_le _ _
  have hmabs : |(y (σ k) - c (σ k)) + (y' (σ k) - c (σ k))| / 2
      = Submission.boxSide k * s := by
    rw [div_eq_iff (by norm_num : (2:ℝ) ≠ 0)]
    rw [hmcoord] at hmk
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)] at hmk
    linarith [hmk]
  have hsum : (|y (σ k) - c (σ k)| + |y' (σ k) - c (σ k)|) / 2
      = Submission.boxSide k * s := by
    have h1 : (|y (σ k) - c (σ k)| + |y' (σ k) - c (σ k)|) / 2
        ≤ Submission.boxSide k * s := by linarith [hyle, hy'le]
    have h2 : Submission.boxSide k * s
        ≤ (|y (σ k) - c (σ k)| + |y' (σ k) - c (σ k)|) / 2 := by
      rw [← hmabs]; linarith [htri]
    linarith [h1, h2]
  have hu : |y (σ k) - c (σ k)| = Submission.boxSide k * s := by linarith [hyle, hsum]
  have hw : |y' (σ k) - c (σ k)| = Submission.boxSide k * s := by linarith [hy'le, hsum]
  rcases abs_eq_abs.mp (hu.trans hw.symm) with h | h
  · exact ⟨k, by linarith [h]⟩
  · by_cases hB0 : Submission.boxSide k * s = 0
    · have hu0 : |y (σ k) - c (σ k)| = 0 := by rw [hu, hB0]
      have hw0 : |y' (σ k) - c (σ k)| = 0 := by rw [hw, hB0]
      exact ⟨k, by have a := abs_eq_zero.mp hu0; have b := abs_eq_zero.mp hw0; linarith⟩
    · exfalso
      have hzero : (y (σ k) - c (σ k)) + (y' (σ k) - c (σ k)) = 0 := by linarith [h]
      have hm0 : |((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y') (σ k) - c (σ k)| = 0 := by
        rw [hmcoord, hzero]; norm_num
      rw [hmk] at hm0
      exact hB0 hm0

/-- **A direction with no vanishing coordinate is not the direction of any straight subsegment of
the box-sphere trace.**  This is exactly the hypothesis `hnc` of
`Work.Drive.Mono.g3_oneEvent_bad_null_nochord` (and the last conjunct of
`Work.Drive.Mono.g3_witnessData_hnoChord`). -/
theorem g3_noChord_of_coord_ne_zero (ψ : Submission.Diffeo) {s : ℝ} (c : R3)
    (σ : Equiv.Perm (Fin 3)) {v : R3} (hv : ∀ k : Fin 3, v (σ k) ≠ 0) :
    ∀ y y' : R3, y ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      y' ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ y = s → Submission.boxNorm c σ y' = s →
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        (1 - t) • y + t • y' ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
        Submission.boxNorm c σ ((1 - t) • y + t • y') = s) →
      (∃ kk : ℝ, y - y' = kk • v) → y = y' := by
  intro y y' _hyc _hy'c hy hy' hseg hpar
  have hseg' := hseg (1 / 2) (by norm_num [Set.mem_Icc])
  have hmid : Submission.boxNorm c σ ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • y') = s := by
    have hc : (1 / 2 : ℝ) • y = (1 - 1 / 2 : ℝ) • y := by norm_num
    rw [hc]
    exact hseg'.2
  obtain ⟨k, hk⟩ := g3_chord_coord_eq c σ hy hy' hmid
  obtain ⟨kk, hkk⟩ := hpar
  have hzero : (y - y') (σ k) = 0 := by
    simp only [PiLp.sub_apply, hk, sub_self]
  rw [hkk] at hzero
  simp only [PiLp.smul_apply, smul_eq_mul] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · rw [h, zero_smul] at hkk
    exact sub_eq_zero.mp hkk
  · exact absurd h (hv k)

/-! ## The face-regularity form `hreg` consumed by `Work.Drive.Mono.ae_slabBoxCrossReg` -/

/-- **`BoxGen`'s face regularity in coordinate form.**  The hypothesis `hreg` of
`Work.Drive.Mono.ae_slabBoxCrossReg` (needed to produce the universal
`Work.Drive.Mono.SlabBoxCrossReg` at a.e. half-width): if `par ψ p` sits on the face
`{y (σ i) = c (σ i) + ε boxSide i * s}`, then the derivative of the pulled-back coordinate
`q ↦ (par ψ q) (σ i)` is non-zero at `p`.

This is `fderiv_par_coord_ne_zero` of `Mono/ae_faceCrossReg_of_boxGen.lean`, which is `private`
there; the consumer `geom3DataAtU_exists` needs a version derived from `BoxGen` alone. -/
theorem g3_hreg_of_boxGen (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ)
    (hBG : Work.Drive.Mono.BoxGen ψ c σ s) :
    ∀ i : Fin 3, i ≠ 2 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ p : ℝ × ℝ,
      (Work.BoxShrink.Pinch.par ψ p) (σ i) = c (σ i) + ε * Submission.boxSide i * s →
      fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p ≠ 0 := by
  intro i _hi ε hε p hp
  have hreg := hBG.1 i ε hε
  have hb : Submission.boxSide i ≠ 0 := ne_of_gt (Submission.boxSide_pos i)
  have hpc : Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i)) p
      = c (σ i) + ε * Submission.boxSide i * s := hp
  have hpull : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.signedFace c σ i) p = ε * s := by
    rw [Work.Smooth.BoxGeneric.pullback_signedFace_eq, hpc]
    rw [show c (σ i) + ε * Submission.boxSide i * s - c (σ i)
        = (ε * s) * Submission.boxSide i from by ring]
    exact mul_div_cancel_right₀ (ε * s) hb
  have hne := (Work.Smooth.Morse.isRegularValue_iff ψ _ _).mp hreg p hpull
  have hchain : fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.signedFace c σ i)) p
      = (Submission.boxSide i)⁻¹ •
        fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p := by
    have hfun : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.signedFace c σ i)
        = fun q : ℝ × ℝ =>
            (Submission.boxSide i)⁻¹ *
              (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i)) q - c (σ i)) := by
      funext q
      rw [Work.Smooth.BoxGeneric.pullback_signedFace_eq, div_eq_mul_inv, mul_comm]
    rw [hfun]
    have hdiff : DifferentiableAt ℝ
        (fun q : ℝ × ℝ => Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i)) q - c (σ i)) p :=
      (((Work.Smooth.Morse.pullback_contDiff ψ (g := fun y : R3 => y (σ i))
          (by fun_prop)).differentiable (by simp)).sub_const (c (σ i))).differentiableAt
    rw [fderiv_const_mul hdiff, fderiv_sub_const]
    rfl
  intro hzero
  apply hne
  rw [hchain, hzero, smul_zero]

/-- **The hypothesis `hreg` of `Work.Drive.Mono.ae_slabBoxCrossReg` from `BoxGen`.** -/
theorem g3_hreg_of_boxGen' (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ)
    (hBG : Work.Drive.Mono.BoxGen ψ c σ s) :
    ∀ i : Fin 3, i ≠ 2 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ p : ℝ × ℝ,
      (Work.BoxShrink.Pinch.par ψ p) (σ i) = c (σ i) + ε * Submission.boxSide i * s →
      fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p ≠ 0 :=
  g3_hreg_of_boxGen ψ c σ s hBG

end

end Work.Drive.Mono
