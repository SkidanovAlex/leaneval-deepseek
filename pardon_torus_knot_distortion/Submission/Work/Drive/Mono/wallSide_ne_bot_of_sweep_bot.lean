import Mathlib
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Mono.wallSideDefs
import Submission.Work.Drive.Mono.noJumpBelowAt_of_noEventAt
import Submission.Work.Drive.Mono.wallDichotomy
import Submission.Work.Drive.Mono.eventValue_mem_window
import Submission.Work.Drive.Mono.eventNoJumpTools
import Submission.Work.Drive.Final.dentOut_trace
import Submission.Work.Drive.Final.dentOut_resolvedCond
import Submission.Work.Drive.Final.noJumpAtAnyEventCond_of_eventTraceData_proved
import Submission.Work.Drive.Final.eventTraceData_holds
import Submission.Work.Drive.Mono.DataPackage
import Submission.Work.Drive.Mono.LevelCountDefs

/-!
# The far side of the wall at an event level is essential

`Work.Drive.Mono.noJumpBelowAt_of_wallSide_ne_bot` (`Mono/eventNoJumpTools.lean`, PROVED) reduces the
(L) field at an event level to the single per-level statement proved here: at a level `lam` of the
window which carries an event of the sweep and at which the region of the sweep has *vanishing*
winding span, the far side `Work.Drive.Mono.wallSide` of the wall has *non-vanishing* winding span.

## The argument

The complement of the wall `T lam = carrier ∩ frontier (tiltedLevelRemoved … lam)` in the surface is
the disjoint union of the region and the far side, and both are open in the carrier
(`Work.Drive.Mono.carrier_sdiff_wall_eq_union`, `Work.Drive.Mono.sweep_subset_interior_removed`), so
the span of the complement of the wall is the supremum of the two spans
(`Work.SurgeryInvariance.Span.union_eq_sup`).  It is therefore enough to find a level `nu < lam`,
in the window and *not* carrying an event, at which the far side is essential: `wallSide nu ⊆ wallSide
lam` (`Work.Drive.Mono.wallSide_mono`), and the span only grows.

Such a `nu` exists as soon as the **no-jump** holds at `lam` (a level just below `lam` at which the
region does not carry the full span, together with a level of the window avoiding the finite set
`exc` of exceptional levels, at which Pardon's dichotomy
(`Work.Drive.Mono.wallSide_dichotomy_of_noEvent`) makes the far side full).  The no-jump at every
event of the sweep is `Work.Drive.Final.NoJumpAtAnyEventCond`, which is produced by the dent route:

* `Work.Drive.Final.eventTraceData_holds` — the per-event dent datum of the `(L)` package (from the
  dent producer `Work.Drive.Final.exists_dentCaptureDepth` and L4b,
  `Work.Drive.Final.dentOutTraceTame` with the event-isolation hypothesis);
* `Work.Drive.Final.noJumpAtAnyEventCond_of_eventTraceData_proved` — the producer of the no-jump.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- **The far side at an event level with vanishing region span is essential, from the no-jump at
every event.**  This is the reduction of the target to `Work.Drive.Final.NoJumpAtAnyEventCond`. -/
theorem wallSide_ne_bot_of_noJumpAtAnyEventCond
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    (hNJ : Work.Drive.Final.NoJumpAtAnyEventCond ψ K s c σ u v h R ℓ)
    {lam : ℝ} (hlam : lam ∈ Set.Icc lam0 lam1)
    (hev : ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam)
    (hbot : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥) :
    Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.Mono.wallSide (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) ≠
        ⊥ := by
  obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexcSub⟩ := hDP.1.tilt
  have hv : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  obtain ⟨pp, hpp, hval⟩ := hev
  -- the level of the event lies strictly inside the window
  have hlev : lam0 < lam := by
    rw [← hval]
    exact Work.Drive.Mono.lam0_lt_eventValue hDP hpp
  have hle1 : lam ≤ lam1 := by
    rw [← hval]
    exact (Work.Drive.Mono.eventValue_mem_window hDP hpp).2
  -- the no-jump at the event level
  have hnj := Work.Drive.Final.noJumpBelowAt_of_noJumpAtAnyEventCond (H := hNJ) hpp
  rw [hval] at hnj
  obtain ⟨mu0, hmu0lt, hbound⟩ := hnj hbot
  -- a non-exceptional level of the window just below `lam`
  obtain ⟨nu, hnu1, hnu2, hnuExc⟩ :=
    Work.Drive.Mono.exists_level_gt_finset exc (a := max mu0 lam0) (b := lam)
      (max_lt hmu0lt hlev)
  have hnuMem : nu ∈ Set.Icc lam0 lam1 :=
    ⟨le_trans (le_max_right _ _) (le_of_lt hnu1), le_of_lt (lt_of_lt_of_le hnu2 hle1)⟩
  have hnuNoEv : ¬ ∃ pp' : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp' ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp') = nu := by
    rintro ⟨pp', hpp', hval'⟩
    exact hnuExc (by rw [← hval']; exact Work.Drive.Mono.eventValue_mem_exc hDP hpp')
  -- Pardon's dichotomy at `nu`
  rcases Work.Drive.Mono.wallSide_dichotomy_of_noEvent p q hp hq hc ψ K himg hcl hDP
      hnuMem hnuNoEv with ⟨htop, -⟩ | ⟨-, hfar⟩
  · -- the region at `nu` is full, contradicting the no-jump at `lam`
    exact absurd htop (hbound nu ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hnu1), hnu2⟩)
  · -- the far side at `nu` is full, and it only grows with the level
    have hmono := Work.Drive.Mono.wallSide_mono (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
      hv hℓne hℓv (le_of_lt hnu2)
    have hle : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Mono.wallSide (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ nu) ≤
        Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Mono.wallSide (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) :=
      Work.SurgeryInvariance.WindingSpan_mono _ hmono
    rw [hfar] at hle
    intro hbot'
    rw [hbot'] at hle
    exact absurd (le_bot_iff.mp hle) (by simp)

/-- **The far side of the wall at an event level of vanishing region span is essential.**

The event structure of the sweep (`hDP`) provides the per-event dent data
`Work.Drive.Final.EventTraceData` of the `(L)` package — through the tameness of the trace of the
deformed level (`Work.Drive.Final.dentOutTraceTameIso_proof`) and the assembly
`Work.Drive.Final.eventTraceData_holds` — hence the no-jump at every event, hence the claim
(`wallSide_ne_bot_of_noJumpAtAnyEventCond`). -/
theorem wallSide_ne_bot_of_sweep_bot
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc lam0 lam1)
    (hev : ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam)
    (hbot : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥) :
    Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.Mono.wallSide (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) ≠
        ⊥ := by
  -- the box of the datum is nonempty, so its radius is positive
  have hs : 0 < s := by
    obtain ⟨⟨y, hyP, -⟩, -⟩ := hDP.1.slabCuts
    have h1 : Submission.boxNorm c σ y < s := (Submission.mem_PBox_iff s c σ y).mp hyP
    have h2 : 0 ≤ Submission.boxNorm c σ y := Submission.boxNorm_nonneg c σ y
    linarith
  -- the per-event dent data of the `(L)` package
  have hET : Work.Drive.Final.EventTraceData ψ K s c σ u v h R ℓ :=
    Work.Drive.Final.eventTraceData_holds (p := p) (q := q) hs hDP
  -- the no-jump at every event
  have hNJ : Work.Drive.Final.NoJumpAtAnyEventCond ψ K s c σ u v h R ℓ :=
    Work.Drive.Final.noJumpAtAnyEventCond_of_eventTraceData_proved p q hp hq hc ψ K himg hcl hDP hET
  exact wallSide_ne_bot_of_noJumpAtAnyEventCond p q hp hq hc ψ K himg hcl hDP hNJ hlam hev hbot

end

end Work.Drive.Mono
