import Mathlib
import Submission.Work.Drive.T6GenAtD
import Submission.Work.Drive.deltaCDesignSet
import Submission.Work.Drive.eventually_goodLoopChain_design
import Submission.Work.Drive.meetBoxForallEventual
import Submission.Work.Drive.diamClause_design_eventually
import Submission.Work.Drive.designLoopFamFamSmooth

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-! ## The cut-avoidance clause of the design, in its two forms -/

/-- **The `∃ δc` clause of `Work.Drive.T6GenAt` at the design's block `k` is
`Work.Drive.DesignCutAvoids`.**  The two statements differ only in the way the swept chain is written
(`Work.Drive.designSweep ... (k + 2)` versus the *definitionally equal* `clampedSweep (cblk (k+2))
(1 - ·) (blockPlane ... (k+2))`), so this is `Iff.rfl`; it is recorded because the openness of the
clause is proved for `DesignCutAvoids` (`Work.Drive.isOpen_designCutAvoids`). -/
theorem designCutAvoids_iff {Q : ℂ → Work.Drive.CappingSpace}
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) :
    Work.Drive.DesignCutAvoids (Q := Q) u cblk k t ↔
      (∃ δc : ℝ, 0 < δc ∧ ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
        x ∉ diskCut (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
          (clampedSweep (cblk (k + 2)) (fun r => 1 - r)
            (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 2)))) :=
  Iff.rfl

/-! ## The `DiamFamReg` clause of the design is the `LoopBoxData` clause of its two loop families -/

/-- **`Work.Drive.DiamFamReg` is the conjunction of the two `LoopBoxData` conditions of the two loop
families** `diamFam` and `arcFam`: the four box clauses of `DiamFamReg` are exactly the four clauses of
the two `LoopBoxData` pairs, in the same order (the two sides differ only by the association of the
conjunctions, so this is a direct combination). -/
theorem designDiamFamReg_iff_loopBoxData {Q : ℂ → Work.Drive.CappingSpace}
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (k : Fin 3)
    (t : EuclideanSpace ℝ (Fin 12)) (θ : ℝ) :
    Work.Drive.DiamFamReg (Work.Drive.designChartT Q u k t) θ (cblk (k + 2))
        (Work.Drive.designPlaneT Q u (k + 2) t) ↔
      (Work.Drive.LoopBoxData (Work.Drive.diamFam (Work.Drive.designChartT Q u k t) θ)
          (Work.Drive.designSweepT Q u cblk (k + 2) t)
        ∧ Work.Drive.LoopBoxData (Work.Drive.arcFam (Work.Drive.designChartT Q u k t) θ)
          (Work.Drive.designSweepT Q u cblk (k + 2) t)) := by
  constructor
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩
  · intro h
    exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

/-- Item §4.3 (openness) of the project lead's `NOTES_LEAD_hodd_blockT6.md`: the set of parameters at
which the design's block `k` satisfies the box-restricted transport bundle `T6GenAtDBox` is **open**.

Ingredients, all on disk: `Work.Drive.eventually_goodLoopChain_design` (the loop clause, proved),
`Work.Drive.eventually_DiamFamRegBox` (the diameter-family clause), the diameter-loop clause (same
shape as the loop clause, to be proved as a helper) and `Work.Drive.isOpen_designCutAvoids`
(`deltaCDesignSet.lean`, the `∃ δc` clause); every clause is open in `t` because the core meet set of
the perturbed block chart is finite, transverse and moves continuously. -/
theorem isOpen_T6GenAtDBox_design {Q : ℂ → Work.Drive.CappingSpace}
    (hQ : Work.Drive.IsChartData Q)
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (k : Fin 3) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) |
      Work.Drive.T6GenAtDBox
        (Work.Drive.blockChart (fun s p => Work.Drive.chartPert s p) Q u
          (fun j => Work.Drive.blk j t) k)
        (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q u
          (fun j => Work.Drive.blk j t) (k + 1))
        (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q u
          (fun j => Work.Drive.blk j t) (k + 2))
        (cblk (k + 1)) (cblk (k + 2))} := by
  rw [isOpen_iff_mem_nhds]
  intro t₀ ht₀
  -- the four clauses of the bundle at `t₀`
  obtain ⟨⟨hcore, hdiam, hcut⟩, hreg⟩ := ht₀
  -- (1) the core-loop clause, from `eventually_goodLoopChain_design`
  have h1 : ∀ᶠ t in 𝓝 t₀, Work.Drive.GoodLoopChain
      (Work.Drive.coreLoop (Work.Drive.blockChart (fun s p => Work.Drive.chartPert s p) Q u
        (fun j => Work.Drive.blk j t) k))
      (Work.Drive.clampedSweep (cblk (k + 1)) (fun r => 1 - r)
        (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q u
          (fun j => Work.Drive.blk j t) (k + 1))) :=
    Work.Drive.eventually_goodLoopChain_design (Q := Q) hQ u cblk k hcore
  -- (2) the diameter-loop clause, from the design smoothness and `eventually_good_meetBox`
  have h2 := diamClause_design_eventually (Q := Q) hQ u cblk k hdiam
  -- (3) the cut-avoidance clause, from the openness of `DesignCutAvoids`
  have h3 : ∀ᶠ t in 𝓝 t₀, Work.Drive.DesignCutAvoids (Q := Q) u cblk k t :=
    (Work.Drive.isOpen_designCutAvoids (Q := Q) hQ u cblk k).mem_nhds
      ((designCutAvoids_iff u cblk k t₀).mpr hcut)
  -- (4) the diameter-family clause at every core meet: first in the `LoopBoxData` form of the two
  -- loop families, then converted back by `designDiamFamReg_iff_loopBoxData`
  have h4 : ∀ᶠ t in 𝓝 t₀, ∀ q ∈ Work.Drive.coreMeet
        (Work.Drive.designChartT Q u k t) (cblk (k + 1))
        (Work.Drive.designPlaneT Q u (k + 1) t),
      Work.Drive.DiamFamReg (Work.Drive.designChartT Q u k t) q.1 (cblk (k + 2))
        (Work.Drive.designPlaneT Q u (k + 2) t) := by
    have hmeet : ∀ t : EuclideanSpace ℝ (Fin 12),
        Work.Drive.coreMeet (Work.Drive.designChartT Q u k t) (cblk (k + 1))
            (Work.Drive.designPlaneT Q u (k + 1) t)
          = Work.Drive.meetBox (Work.Drive.coreLoop (Work.Drive.designChartT Q u k t))
            (Work.Drive.designSweepT Q u cblk (k + 1) t) := fun t => rfl
    have hR : ∀ᶠ t in 𝓝 t₀, ∀ q ∈ Work.Drive.meetBox
          (Work.Drive.coreLoop (Work.Drive.designChartT Q u k t))
          (Work.Drive.designSweepT Q u cblk (k + 1) t),
        (Work.Drive.LoopBoxData (Work.Drive.diamFam (Work.Drive.designChartT Q u k t) q.1)
            (Work.Drive.designSweepT Q u cblk (k + 2) t)
          ∧ Work.Drive.LoopBoxData (Work.Drive.arcFam (Work.Drive.designChartT Q u k t) q.1)
            (Work.Drive.designSweepT Q u cblk (k + 2) t)) := by
      refine Work.Drive.eventually_forall_meetBox_of_eventually_smooth (p₀ := t₀)
        (L := fun t θ => Work.Drive.coreLoop (Work.Drive.designChartT Q u k t) θ)
        (D := fun t x => Work.Drive.designSweepT Q u cblk (k + 1) t x)
        (Work.Drive.contMDiff_coreLoop_design k u hQ.1)
        (Work.Drive.contMDiff_designSweepT (k + 1) u cblk hQ.1)
        (fun t θ => (Work.Drive.LoopBoxData (Work.Drive.diamFam (Work.Drive.designChartT Q u k t) θ)
              (Work.Drive.designSweepT Q u cblk (k + 2) t)
            ∧ Work.Drive.LoopBoxData (Work.Drive.arcFam (Work.Drive.designChartT Q u k t) θ)
              (Work.Drive.designSweepT Q u cblk (k + 2) t)))
        ?hprop
      · intro ξ hξ
        have hbase : Work.Drive.LoopBoxData
              (Work.Drive.diamFam (Work.Drive.designChartT Q u k t₀) ξ.1)
              (Work.Drive.designSweepT Q u cblk (k + 2) t₀)
            ∧ Work.Drive.LoopBoxData
              (Work.Drive.arcFam (Work.Drive.designChartT Q u k t₀) ξ.1)
              (Work.Drive.designSweepT Q u cblk (k + 2) t₀) :=
          (designDiamFamReg_iff_loopBoxData u cblk k t₀ ξ.1).mp
            (by simpa only [Work.Drive.designChartT, Work.Drive.designPlaneT] using hreg ξ hξ)
        exact Work.Drive.loopBoxData_eventually_at
          (p₀ := ((t₀, ξ.1) : EuclideanSpace ℝ (Fin 12) × ℝ))
          (A := fun p => Work.Drive.diamFam (Work.Drive.designChartT Q u k p.1) p.2)
          (A' := fun p => Work.Drive.arcFam (Work.Drive.designChartT Q u k p.1) p.2)
          (D := fun p => Work.Drive.designSweepT Q u cblk (k + 2) p.1)
          (Work.Drive.contMDiff_diamFam_loopFam_design k u hQ.1)
          (Work.Drive.contMDiff_arcFam_loopFam_design k u hQ.1)
          (Work.Drive.contMDiff_designSweepT_fam (k + 2) u cblk hQ.1)
          hbase.1 hbase.2
    refine hR.mono fun t ht q hq => ?_
    exact (designDiamFamReg_iff_loopBoxData u cblk k t q.1).mpr (ht q (hmeet t ▸ hq))
  -- the four clauses are the bundle
  filter_upwards [h1, h2, h3, h4] with t h1t h2t h3t h4t
  refine ⟨⟨h1t, h2t, (designCutAvoids_iff u cblk k t).mp h3t⟩, ?_⟩
  simpa only [Work.Drive.designChartT, Work.Drive.designPlaneT, Work.Drive.designSweepT] using h4t

end

end Work.Drive
