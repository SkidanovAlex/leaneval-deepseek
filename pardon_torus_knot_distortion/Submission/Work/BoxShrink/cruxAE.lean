import Mathlib
import Submission.Work.BoxShrink.assemble
import Submission.Work.BoxShrink.sweepNice_of_ae
import Submission.Work.BoxShrink.Pinch.Migrated
import Submission.Work.BoxSweep.sweep
import Submission.Work.Smooth.RepairImport.All
import Submission.Work.Smooth.OneManifold.All
import Submission.Work.Smooth.Schoenflies.All
import Submission.Work.Topology.Classical.cleanOneCurve_of_pushThroughInnermost
import Submission.Work.Topology.SphereSlicing.cleanOneCurve_map_homeomorph_iff
import Submission.Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve

/-!
# Pardon's cut-and-paste from the classical input, and the almost-everywhere plane levels

Two auxiliary results about *inputs*.

## 1. `cleansDiscsAll_of_pushThrough`

Pardon's cut-and-paste at the surface, `Work.InnermostDisk.CleansDiscs (mapHomeomorph ψ)` for every
`ψ`, from the single classical statement
`Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard` (Alexander's theorem for an
embedded `2`-sphere in `ℝ³` plus isotopy extension).  The passage is pure bookkeeping:
`PushThroughInnermost → CleanOneCurve`
(`Work.Topology.Classical.cleanOneCurve_of_pushThroughInnermost`),
`CleanOneCurve standard ↔ CleanOneCurve (mapHomeomorph ψ)`
(`Work.Topology.SphereSlicing.cleanOneCurve_map_homeomorph_iff`), and
`CleanOneCurve → CleansDiscs` (`Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve`).

## 2. `AePlaneCleaned`, `exists_plane_level_of_ae`

`AePlaneCleaned` is the almost-everywhere general position of the *cleaning* of the flat disc cut out
of the box by the cutting plane — proved from Pardon's cut-and-paste in `Submission/Work/PlaneSlice`
(`Work.PlaneSlice.aePlaneCleaned_of_pushThrough`, for the `AePlaneCleaned` defined here; the
`PlaneSlice` chapter imports this file, so the bridge lives in the ledger) — and
`exists_plane_level_of_ae` is the sweep lemma which picks a plane level `u` lying simultaneously in a
conull set and where the one-dimensional coarea bound holds.

NOTE.  An earlier version of this file also carried a rewritten crux (`CruxCoreAE`, `SweepNiceAE`,
`cruxCoreAE_of_smoothHalfS`, `sweepNiceAE_of_ae`, `boxShrink_of_cruxAE`) which chose the plane level
in general position and obtained the double bubble from `Work.BoxShrink.Pinch.SmoothHalfS`.  That
datum is **FALSE** — `Work.BoxShrink.PinchOff.not_smoothHalfS : ¬ Pinch.SmoothHalfS`, refuted at the
"tangent configuration" of the standard torus — so the whole route was vacuous and has been removed.
The ledger uses the *counted* form (`Work.BoxShrink.Pinch.CountingHalf`) instead.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal Topology

namespace Work.BoxShrink

noncomputable section

/-- **Pardon's cut-and-paste step at the surface, from the classical cut-and-paste at the standard
torus.** -/
theorem cleansDiscsAll_of_pushThrough
    (h : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    CleansDiscsAll :=
  fun ψ => Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve
    ((Work.Topology.SphereSlicing.cleanOneCurve_map_homeomorph_iff ψ.toHomeomorph).mpr
      (Work.Topology.Classical.cleanOneCurve_of_pushThroughInnermost h))

/-! ## A plane level that is both of small count and cleaned -/

/-- **A level of the cutting plane exists both in a conull set and where the integral bound holds.**

This is `Work.BoxSweep.exists_plane_level` with the pigeonhole of
`Work.BoxShrink.exists_of_ae_and_lintegral` in place of the bare pigeonhole: if `A` is conull then
some level `u ∈ (-ε r, ε r)` lies in `A` and satisfies the count bound. -/
theorem exists_plane_level_of_ae (K : Knot) (c : R3) (σ : Equiv.Perm (Fin 3)) {d r s : ℝ}
    (hd : 0 ≤ d) (hbound : Work.Sweep.IsDistortionBound K d) (hr : 0 < r) (hs : 0 < s)
    (hsr : s ≤ (1 + Submission.eps) * r) {A : Set ℝ}
    (hA : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), A u) :
    ∃ u ∈ Set.Ioo (-(Submission.eps * r)) (Submission.eps * r), A u ∧
      ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
        ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) := by
  classical
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  set ρ : ℝ := Submission.eps * r with hρ
  have hρpos : 0 < ρ := mul_pos Submission.eps_pos hr
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ K.curve t ∈ Submission.PBox s c σ}
    with hS
  have hSmeas : MeasurableSet S :=
    measurableSet_Icc.inter
      ((Work.BoxSweep.isOpen_PBox s c σ).measurableSet.preimage K.smooth.continuous.measurable)
  have hSsub : S ⊆ Set.Icc (0 : ℝ) (2 * Real.pi) := fun _ ht => ht.1
  set w : ℝ → ENNReal := (Set.Ioo (-ρ) ρ).indicator (fun _ => (1 : ENNReal)) with hwdef
  have hwmeas : AEMeasurable w := (measurable_const.indicator measurableSet_Ioo).aemeasurable
  have hcoa := Work.Sweep.lintegral_mul_levelCount_le_subset (a := 0) (b := 2 * Real.pi) hπ
    hSmeas hSsub (w := w) hwmeas (fun t _ => Work.BoxSweep.planeFun_hasDerivAt K c σ t)
    (Work.BoxSweep.continuousOn_planeDeriv K c σ)
  have hLHS : ∫⁻ y, w y * Work.Sweep.levelCount (Work.BoxSweep.planeFun K c σ) S y
      = ∫⁻ u in Set.Ioo (-ρ) ρ, Work.Sweep.levelCount (Work.BoxSweep.planeFun K c σ) S u := by
    rw [hwdef]
    rw [show (fun y : ℝ => (Set.Ioo (-ρ) ρ).indicator (fun _ => (1 : ENNReal)) y *
          Work.Sweep.levelCount (Work.BoxSweep.planeFun K c σ) S y)
        = (Set.Ioo (-ρ) ρ).indicator
            (fun y => Work.Sweep.levelCount (Work.BoxSweep.planeFun K c σ) S y)
        from ?_]
    · exact MeasureTheory.lintegral_indicator measurableSet_Ioo _
    · funext y
      by_cases hy : y ∈ Set.Ioo (-ρ) ρ <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
  rw [hLHS] at hcoa
  have hRHS : ∫⁻ t in S, ENNReal.ofReal |Work.BoxSweep.planeDeriv K σ t|
        * w (Work.BoxSweep.planeFun K c σ t) ≤ ENNReal.ofReal (10 * d * s) := by
    have hw1 : ∀ t ∈ S, w (Work.BoxSweep.planeFun K c σ t) ≤ (1 : ENNReal) := by
      intro t _
      rw [hwdef]
      by_cases hb : Work.BoxSweep.planeFun K c σ t ∈ Set.Ioo (-ρ) ρ <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hb]
    have hpt : ∀ t ∈ S, ENNReal.ofReal |Work.BoxSweep.planeDeriv K σ t|
        * w (Work.BoxSweep.planeFun K c σ t) ≤ ENNReal.ofReal (speed K t) := by
      intro t ht
      refine (mul_le_mul' (ENNReal.ofReal_le_ofReal (Work.BoxSweep.abs_planeDeriv_le_speed K σ t))
        (hw1 t ht)).trans ?_
      rw [mul_one]
    have h1 : ∫⁻ t in S, ENNReal.ofReal |Work.BoxSweep.planeDeriv K σ t|
        * w (Work.BoxSweep.planeFun K c σ t) ≤ Work.Sweep.arclengthIn K S := by
      rw [Work.Sweep.arclengthIn]
      exact Work.BoxSweep.setLIntegral_mono_aux hSmeas hpt
    have h2 : Work.Sweep.arclengthIn K S
        ≤ Work.Sweep.arclengthIn K
            (Work.Sweep.paramSetIn K (Metric.closedBall c (5 / 2 * s))) := by
      refine Work.Sweep.arclengthIn_mono K fun t ht => ?_
      have hmem : K.curve t ∈ Submission.PBox s c σ := ht.2
      have hball := Submission.PBox_subset_ball s hs.le c σ hmem
      exact ⟨Metric.ball_subset_closedBall hball, ht.1⟩
    have h3 : Work.Sweep.arclengthIn K (Work.Sweep.paramSetIn K (Metric.closedBall c (5 / 2 * s)))
        ≤ ENNReal.ofReal (10 * d * s) := by
      refine (Work.Sweep.arclengthIn_closedBall_le (K := K) hd hbound c (R := 5 / 2 * s)).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      ring_nf
      linarith
    exact h1.trans (h2.trans h3)
  have hle : ENNReal.ofReal (10 * d * s)
      ≤ ENNReal.ofReal ((5 * (1 + Submission.eps) / Submission.eps * d) * (ρ - (-ρ))) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have heps : Submission.eps ≠ 0 := ne_of_gt Submission.eps_pos
    have hρeq : ρ = Submission.eps * r := hρ
    rw [hρeq]
    have : (5 * (1 + Submission.eps) / Submission.eps * d)
        * (Submission.eps * r - -(Submission.eps * r)) = 10 * (1 + Submission.eps) * d * r := by
      field_simp
      ring
    rw [this]
    nlinarith [hd, hsr, hr, Submission.eps_pos]
  have hInt : ∫⁻ u in Set.Ioo (-ρ) ρ, Work.Sweep.levelCount (Work.BoxSweep.planeFun K c σ) S u
      ≤ ENNReal.ofReal ((5 * (1 + Submission.eps) / Submission.eps * d) * (ρ - (-ρ))) :=
    hcoa.trans (hRHS.trans hle)
  have hint : ∀ y : ℝ, Work.Sweep.levelCount (Work.BoxSweep.planeFun K c σ) S y = ⊤ ∨
      ∃ k : ℕ, Work.Sweep.levelCount (Work.BoxSweep.planeFun K c σ) S y = (k : ENNReal) :=
    fun y => Work.BoxSweep.levelCount_eq_top_or_nat (Work.BoxSweep.planeFun K c σ) S y
  have hC0 : 0 ≤ 5 * (1 + Submission.eps) / Submission.eps * d := by
    have h' : 5 * (1 + Submission.eps) / Submission.eps = 75 / 2 := by norm_num [Submission.eps]
    rw [h']
    positivity
  obtain ⟨u, hu, hAu, huC⟩ := exists_of_ae_and_lintegral
    (f := Work.Sweep.levelCount (Work.BoxSweep.planeFun K c σ) S) (A := A)
    (a := -ρ) (b := ρ) (C := 5 * (1 + Submission.eps) / Submission.eps * d)
    (by linarith) hC0 hint hA hInt
  refine ⟨u, hu, hAu, ?_⟩
  have hsub : {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}
      ⊆ S ∩ (Work.BoxSweep.planeFun K c σ) ⁻¹' {u} := by
    intro t ht
    refine ⟨⟨Set.Ico_subset_Icc_self ht.1, ht.2.1⟩, ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Work.BoxSweep.planeFun]
    linarith [ht.2.2]
  calc ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal))
      ≤ ((↑(Set.encard (S ∩ (Work.BoxSweep.planeFun K c σ) ⁻¹' {u})) : ENNReal)) :=
        ENat.toENNReal_le.mpr (Set.encard_le_encard hsub)
    _ = Work.Sweep.levelCount (Work.BoxSweep.planeFun K c σ) S u := rfl
    _ ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d) := huC

/-! ## The almost-everywhere cleaning of the cutting disc -/

/-- **Almost every cutting plane gives a cleaned flat disc.**

The cutting disc `cutDisc s c σ u = PBox s c σ ∩ {y | y (σ 2) = c (σ 2) + u}` is the flat disc of
Pardon's double bubble.  For almost every `u` the plane `{y (σ 2) = c (σ 2) + u}` meets the smooth
surface in a finite union of circles, and at such a level Pardon's planar innermost argument cleans
the disc (`Submission/Work/PlaneSlice`,
`Work.PlaneSlice.aePlaneCleaned_of_pushThrough`). -/
def AePlaneCleaned : Prop :=
  ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ),
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Core.cutDisc s c σ u)

end

end Work.BoxShrink
