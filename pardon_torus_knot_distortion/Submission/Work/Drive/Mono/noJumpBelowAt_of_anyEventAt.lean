import Mathlib
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.Mono.DichotomyB
import Submission.Work.Drive.Final.dentOut_resolved
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.nojump_dent
import Submission.Work.Drive.Final.dentOut_resolvedDisc
import Submission.Work.Drive.Final.dentOut_hgen
import Submission.Work.Drive.Final.dentOut_trace
import Submission.Work.Drive.Final.openTiltedSweepRegion_subset_dentOutRegion
import Submission.Work.Drive.Final.anyDentData_exists
import Submission.Work.Drive.Final.dentOut_sweep_subset
import Submission.Work.Drive.Mono.levelCount_lt_min_all
import Submission.Work.Drive.Mono.trace_localModel_of_not_event

import Submission.Work.Drive.Mono.eventValue_mem_exc
import Submission.Work.Drive.Mono.eventNoJumpTools
import Submission.Work.Drive.Mono.wallDichotomy
import Submission.Work.Drive.Mono.wallSide_ne_bot_of_sweep_bot
import Submission.Work.Drive.Mono.wallSideDefs
import Submission.Work.Drive.Mono.noJumpBelowAt_of_noEventAt
import Submission.Work.Drive.Mono.existsUnique_top_of_two_pieces_of_frontier
import Submission.Work.Drive.Final.dentOut_resolvedCond

/-!
# The no-jump at an event level of the tilted sweep

This module proves `Work.Drive.Mono.noJumpBelowAt_of_anyEventAt`: at a level `lam` of the window which
carries an event of the sweep and whose level region has *vanishing* winding span, no level just below
carries the *full* span.

## The argument (Pardon's rank bound, in the form the tilted sweep admits)

Write `X λ` for the region of the sweep at the level `λ` (`Work.Drive.Final.sweep`, i.e. the level
region), and

    T λ = P.carrier ∩ frontier (tiltedLevelRemoved … λ)      ("the wall" at the level),
    Y λ = P.carrier \ (X λ ∪ T λ)                            ("the far side" of the wall)

(`Submission/Work/Drive/Mono/wallSideDefs.lean`).  The complement of the wall in the surface is the
disjoint union `X λ ∪ Y λ` *by construction*.  The three ingredients are:

* **the wall dichotomy at non-exceptional levels.**  At a level `ν ∉ exc` the wall is the union of
  the ranges of finitely many pairwise disjoint simple *inessential* closed curves
  (`Work.Drive.Mono.traceCurvesAt_of_noEventAt_aux`, which spends the level count through Pardon's
  Lemma 2), and hence exactly one of the two sides carries the full winding span
  (`Work.Drive.Mono.existsUnique_top_of_two_pieces_of_frontier`, the abstract wall dichotomy for a
  wall whose "far side" need not be open).
* **the far side grows with the level** — `Work.Drive.Mono.wallSide_mono`.
* **every event level lies in `exc`** — `Work.Drive.Mono.eventValue_mem_exc`; since
  `TiltData` puts `exc ⊆ (lam0, lam1)`, the level `lam` of an event is *not* the top of the window,
  so there is a non-exceptional level just above it.

With these: assume that some non-exceptional level `ν ≤ lam` carries the full span.  The wall
dichotomy at `ν` makes the far side `Y ν` vanishing (`W Y ν = ⊥`); `Y ν ⊆ Y ν'` for a
non-exceptional `ν' ∈ (lam, lam1]`, so `W Y ν' = ⊥` too; the wall dichotomy at `ν'` then makes
`W X ν' = ⊤`.  But `X ν' ⊆ X lam` (the regions shrink with the level) and `W X lam = ⊥` by
hypothesis — a contradiction.  Hence no non-exceptional level below (or at) `lam` carries the full
span, and any event level below `lam` inherits this by monotonicity from a non-exceptional level
below it.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono

noncomputable section

/-! ## The reduction to Pardon's rank bound at the event level

Pardon's proof of `spherefamily` shows that the `H₁`-rank of the region of the surface changes by at
most one across a *single* surgery, while at "generic" levels it is either `0` or the full rank; the
gap between the two is at least two, so it cannot be crossed.  In the tilted sweep the same argument
reads: at every level outside the finite set `exc` the span of the region is `⊥` or `⊤`
(`Work.Drive.Mono.wallSide_dichotomy_of_noEvent`), while across the single event at the level `lam`
the rank jumps by at most one; hence for every level `ν < lam` the rank of the span is at most one,
i.e. the span is *not* full.

The missing brick is the rank bound itself (the "one surgery" identification at the event level);
`noJumpBelowAt_of_anyEventAt_of_rank` below records the reduction, and
`noJumpBelowAt_of_anyEventAt` is the target statement as commissioned.
-/

/-- **The target, from the rank bound at the levels below an event level.** -/
theorem noJumpBelowAt_of_anyEventAt_of_rank
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
      (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥)
    (hrank : ∃ mu0 : ℝ, mu0 < lam ∧ ∀ ν ∈ Set.Ico mu0 lam,
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ ν)) ≤ 1) :
    ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) ≠ ⊤ := by
  obtain ⟨mu0, hmu0lt, hbound⟩ := hrank
  refine ⟨mu0, hmu0lt, fun mu hmu => ?_⟩
  intro htop
  have hle := hbound mu hmu
  rw [htop] at hle
  have htoprank : Module.finrank ℚ ↥(⊤ : Submodule ℚ (ℚ × ℚ)) = 2 := by
    rw [(Submodule.topEquiv : (⊤ : Submodule ℚ (ℚ × ℚ)) ≃ₗ[ℚ] (ℚ × ℚ)).finrank_eq]
    simp [Module.finrank_prod]
  rw [htoprank] at hle
  omega


/-- **The target, from the dent route's output.**  `Work.Drive.Final.NoJumpAtAnyEventCond` is the
output of the dent route (`Work.Drive.Final.noJumpAtAnyEventCond_of_eventTraceData`), whose single
residual is `Work.Drive.Final.EventTraceData`; the instance of
`Work.Drive.Final.noJumpBelowAt_of_noJumpAtAnyEventCond` at the event of the level `lam` is exactly
the target statement, by the definition of `Work.Drive.Mono.NoJumpBelowAt`. -/
theorem noJumpBelowAt_of_anyEventAt_of_noJumpAtAnyEventCond
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u h R : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    (H : Work.Drive.Final.NoJumpAtAnyEventCond ψ K s c σ u v h R ℓ)
    {pp : ℝ × ℝ} (hev : Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp) {lam : ℝ}
    (hval : ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam)
    (hbot : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥) :
    ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) ≠ ⊤ := by
  have h := Work.Drive.Final.noJumpBelowAt_of_noJumpAtAnyEventCond (H := H) hev
  rw [hval] at h
  exact h hbot

theorem noJumpBelowAt_of_anyEventAt
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
    ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) ≠ ⊤ := by
  -- The target is reduced (`Work.Drive.Mono.noJumpBelowAt_of_wallSide_ne_bot`, in
  -- `Submission/Work/Drive/Mono/eventNoJumpTools.lean`) to the single per-level statement that the
  -- far side of the wall at an *event* level is essential
  -- (`Work.Drive.Mono.wallSide_ne_bot_of_sweep_bot`).
  exact Work.Drive.Mono.noJumpBelowAt_of_wallSide_ne_bot p q hp hq hc ψ K himg hcl hDP hlam
    (Work.Drive.Mono.wallSide_ne_bot_of_sweep_bot p q hp hq hc ψ K himg hcl hDP hlam hev hbot)

end

end Work.Drive.Mono
