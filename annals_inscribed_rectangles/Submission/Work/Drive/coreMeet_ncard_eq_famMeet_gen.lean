import Mathlib
import Submission.Work.Drive.coreCountFam
import Submission.Work.Drive.famMeetDefs
import Submission.Work.Drive.coreMeet_ncard_eq_famMeet

namespace Work.Drive

/-!
# The general form of `coreMeet_ncard_eq_famMeet`: the chart moves with `t`

`Work.Drive.coreMeet_ncard_eq_famMeet` identifies the design's count
`coreMeet Q c (P t)` with the family meet set `famMeet (coreLoopFam Q) (sweepFam c (1 - ·) P) t` for a
*constant* chart `Q`.  When the chart itself depends on the perturbation parameter,
`Q : ℝ → ℂ → CappingSpace`, the same identification holds verbatim with `chartLoopFam Q` in place of
`coreLoopFam Q` — the only difference being that the loop side of the family also reads its chart from
the first coordinate:

`famLoop (chartLoopFam Q) p = coreLoop (Q (p 0)) (p 1)`.

Everything else (the coordinate bookkeeping of `famOfPair`/`pairOfFam`, the box membership and the
chain side) is reused from `Submission/Work/Drive/coreMeet_ncard_eq_famMeet.lean`.
-/

noncomputable section

/-- The loop side of `chartLoopFam Q` on the five-box: `p ↦ coreLoop (Q (p 0)) (p 1)`.  The family
parameter `p 0` selects the chart *and* the presentation; `p 1` is the loop parameter. -/
lemma famLoop_chartLoopFam (Q : ℝ → ℂ → CappingSpace) (p : EuclideanSpace ℝ (Fin 5)) :
    famLoop (chartLoopFam Q) p = coreLoop (Q (p 0)) (p 1) := by
  simp [famLoop, chartLoopFam, mk2]

/-- **The design's count is a `famMeet`, with the chart moving too**: for `t ∈ [0,1]`, the meet set
`Work.Drive.coreMeet (Q t) c (P t)` of the core loop of the `t`-th chart with the clamped sweep of the
`t`-th plane presentation has the same cardinality as
`Work.Drive.famMeet (chartLoopFam Q) (sweepFam c (fun s => 1 - s) P) t`, under the bijection
`q ↦ (t, q.1, q.2 0, q.2 1, q.2 2)`.  This is the general form of
`Work.Drive.coreMeet_ncard_eq_famMeet` (there the chart is constant) and is what makes the design's
count — `designCount Q A A' c ψ u = Odd (coreSideCount (linCapping A ∘ Q) c (linCapping A' ∘
rotPresentation Q u))`, where *both* the chart and the sweep depend on the perturbation — an instance of
the L6 engine `Work.Drive.odd_ncard_famMeet_iff`.  The hypothesis `ht` is necessary: `unitBox 4`
constrains `p 0 = t`, so `famMeet L N t = ∅` for `t ∉ [0,1]`, while `coreMeet` does not depend on `t`
except through `Q t` and `P t`. -/
theorem coreMeet_ncard_eq_famMeet_gen (Q : ℝ → ℂ → Work.Drive.CappingSpace) (c : ℝ)
    (P : ℝ → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (Work.Drive.coreMeet (Q t) c (P t)).ncard
      = (Work.Drive.famMeet (Work.Drive.chartLoopFam Q)
          (Work.Drive.sweepFam c (fun s => 1 - s) P) t).ncard := by
  refine Set.ncard_congr (fun q _ => famOfPair t q) ?_ ?_ ?_
  · -- the map sends a `coreMeet` point into the family box
    intro q hq
    rw [coreMeet, Set.mem_ofPred_eq] at hq
    obtain ⟨hq1, hq2, hqeq⟩ := hq
    rw [famMeet, Set.mem_ofPred_eq]
    refine ⟨?_, ?_, ?_⟩
    · exact famOfPair_mem_unitBox t ht q hq1 hq2
    · rw [famOfPair_apply_zero]
    · rw [famLoop_chartLoopFam, famChain_sweepFam]
      rw [famOfPair_apply_zero, famOfPair_apply_one, famT3_famOfPair_tail]
      exact hqeq
  · -- injectivity
    intro q q' _ _ heq
    exact famOfPair_injective t heq
  · -- surjectivity
    intro p hp
    rw [famMeet, Set.mem_ofPred_eq] at hp
    obtain ⟨hpbox, hp0, hpe⟩ := hp
    refine ⟨pairOfFam p, ?_, ?_⟩
    · rw [coreMeet, Set.mem_ofPred_eq]
      refine ⟨?_, ?_, ?_⟩
      · rw [pairOfFam_fst]; exact hpbox 1
      · rw [Submission.Drive.unitBox, Set.mem_ofPred_eq]
        intro i
        rw [pairOfFam_snd_apply]
        exact hpbox i.succ.succ
      · have he : coreLoop (Q t) (p 1)
            = clampedSweep c (fun s => 1 - s) (P t) (famT3 (p 2) (p 3) (p 4)) := by
          have h := hpe
          rw [famLoop_chartLoopFam, famChain_sweepFam, hp0] at h
          exact h
        rw [pairOfFam_fst, pairOfFam_snd, he]
    · exact famOfPair_pairOfFam t p hp0

end

end Work.Drive
