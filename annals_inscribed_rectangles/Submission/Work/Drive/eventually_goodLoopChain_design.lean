import Mathlib
import Submission.Work.Drive.T6GenAtDefs
import Submission.Work.Drive.goodPair_pertChart_isOpen
import Submission.Work.Drive.perturbedTripleIdentity
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.exists_chartPert

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

noncomputable section

/-- The exponential parametrisation of the core loop is smooth. -/
lemma contMDiff_coreLoop_exp : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) Ctop
    (fun t : ℝ => Complex.exp (Real.pi * (t : ℂ) * Complex.I)) := by
  rw [contMDiff_iff_contDiff]
  refine Complex.contDiff_exp.comp ?_
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const

/-- The rotated plane presentation of a smooth chart is smooth. -/
lemma contMDiff_rotPresentation_of_contMDiff {Q : ℂ → CappingSpace} (w : UnitAddCircle)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) :
    ContMDiff (𝓡 2) (𝓡 4) Ctop (rotPresentation Q w) :=
  contMDiff_diskPlane ((contMDiff_rotCappingAngle w).comp hQ)

/-- **The loop family of the design's block `k` is jointly smooth in the design parameter.** -/
lemma contMDiff_designLoopFam (k : Fin 3) (t₀ : EuclideanSpace ℝ (Fin 12))
    (u : Fin 3 → UnitAddCircle) {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℝ)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × ℝ =>
        chartPert (blk k (t₀ + q.1))
          (rotCapping (u k) (Q (Complex.exp (Real.pi * (q.2 : ℂ) * Complex.I))))) := by
  have hG1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℝ)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × ℝ => blk k (t₀ + q.1)) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hG2 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℝ)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × ℝ =>
        rotCapping (u k) (Q (Complex.exp (Real.pi * (q.2 : ℂ) * Complex.I)))) :=
    (contMDiff_rotCappingAngle (u k)).comp
      (hQ.comp (contMDiff_coreLoop_exp.comp (contMDiff_iff_contDiff.mpr (by fun_prop))))
  have hmain := contMDiff_chartPert.comp (hG1.prodMk hG2)
  refine hmain.congr fun q => ?_
  simp only [Function.comp_apply]

/-- **The chain family of the design's block `k+1` is jointly smooth in the design parameter.** -/
lemma contMDiff_designChainFam (k : Fin 3) (t₀ : EuclideanSpace ℝ (Fin 12))
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
        clampedSweep (cblk (k + 1)) (fun r => 1 - r)
          (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j (t₀ + q.1)) (k + 1))
          q.2) := by
  have hrot : ContMDiff (𝓡 2) (𝓡 4) Ctop (rotPresentation Q (u (k + 1))) :=
    contMDiff_rotPresentation_of_contMDiff (u (k + 1)) hQ
  have hPp : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2)))
      (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
        chartPert (blk (k + 1) (t₀ + q.1)) (rotPresentation Q (u (k + 1)) q.2)) := by
    have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2)))
        (𝓡 4) Ctop
        (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
          blk (k + 1) (t₀ + q.1)) :=
      contMDiff_iff_contDiff.mpr (by fun_prop)
    have h2 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2)))
        (𝓡 4) Ctop
        (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 2) =>
          rotPresentation Q (u (k + 1)) q.2) :=
      hrot.comp (contMDiff_iff_contDiff.mpr (by fun_prop))
    have hmain := contMDiff_chartPert.comp (h1.prodMk h2)
    refine hmain.congr fun q => ?_
    simp only [Function.comp_apply]
  have hmain := contMDiff_clampedSweep_family_gen (P := EuclideanSpace ℝ (Fin 12))
    (cblk (k + 1)) (fun r : ℝ => 1 - r) (by fun_prop)
    (fun q (y : EuclideanSpace ℝ (Fin 2)) =>
      chartPert (blk (k + 1) (t₀ + q)) (rotPresentation Q (u (k + 1)) y)) hPp
  refine hmain.congr fun q => ?_
  rfl

/-- Item §5 P2 (openness) of the project lead's `NOTES_LEAD_hdense.md`: the `GoodLoopChain` clause of
`T6GenAt` at the design's block `k` is *open* in the design parameter `t`.  This is
`Work.Drive.eventually_good_meetBox` applied to the design's family
`t ↦ (coreLoop (blockChart Ξc Q u (τ t) k), clampedSweep (cblk (k+1)) (1-·) (blockPlane Ξc Q u (τ t) (k+1)))`
after shifting the parameter to `t₀`; the joint smoothness of the family in `t` is the input the
prover has to assemble from the chart-perturbation chain lemmas (`contMDiff_chartPert`, linearity of
`blk`). -/
theorem eventually_goodLoopChain_design {Q : ℂ → Work.Drive.CappingSpace}
    (hQ : Work.Drive.IsChartData Q)
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (k : Fin 3)
    {t₀ : EuclideanSpace ℝ (Fin 12)}
    (h : Work.Drive.GoodLoopChain
      (Work.Drive.coreLoop (Work.Drive.blockChart (fun s p => Work.Drive.chartPert s p) Q u
        (fun j => Work.Drive.blk j t₀) k))
      (Work.Drive.clampedSweep (cblk (k + 1)) (fun r => 1 - r)
        (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q u
          (fun j => Work.Drive.blk j t₀) (k + 1)))) :
    Filter.Eventually (fun t : EuclideanSpace ℝ (Fin 12) =>
      Work.Drive.GoodLoopChain
        (Work.Drive.coreLoop (Work.Drive.blockChart (fun s p => Work.Drive.chartPert s p) Q u
          (fun j => Work.Drive.blk j t) k))
        (Work.Drive.clampedSweep (cblk (k + 1)) (fun r => 1 - r)
          (Work.Drive.blockPlane (fun s p => Work.Drive.chartPert s p) Q u
            (fun j => Work.Drive.blk j t) (k + 1))))
      (nhds t₀) := by
  set L : EuclideanSpace ℝ (Fin 12) → ℝ → CappingSpace :=
    fun q t => coreLoop (blockChart (fun s p => chartPert s p) Q u (fun j => blk j (t₀ + q)) k) t
    with hLdef
  set D : EuclideanSpace ℝ (Fin 12) → EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun q x => clampedSweep (cblk (k + 1)) (fun r => 1 - r)
      (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j (t₀ + q)) (k + 1)) x
    with hDdef
  have hL : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × ℝ)) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × ℝ => L q.1 q.2) := by
    refine (contMDiff_designLoopFam k t₀ u hQ.1).congr fun q => ?_
    simp only [hLdef, coreLoop, blockChart]
  have hD : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) => D q.1 q.2) := by
    refine (contMDiff_designChainFam k t₀ u cblk hQ.1).congr fun q => ?_
    simp only [hDdef]
  have h0 : GoodLoopChain (L 0) (D 0) := by
    have hL0 : L 0 = coreLoop (blockChart (fun s p => chartPert s p) Q u
        (fun j => blk j t₀) k) := by
      funext s
      simp only [hLdef, add_zero]
    have hD0 : D 0 = clampedSweep (cblk (k + 1)) (fun r => 1 - r)
        (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t₀) (k + 1)) := by
      funext x
      simp only [hDdef, add_zero]
    rw [hL0, hD0]
    exact h
  have hEv := eventually_good_meetBox L D hL hD h0.1 h0.2.1 h0.2.2
  have hEv' : ∀ᶠ q in 𝓝 (0 : EuclideanSpace ℝ (Fin 12)), GoodLoopChain (L q) (D q) := by
    simpa only [GoodLoopChain] using hEv
  have htend : Tendsto (fun t : EuclideanSpace ℝ (Fin 12) => t - t₀) (𝓝 t₀)
      (𝓝 (0 : EuclideanSpace ℝ (Fin 12))) := by
    simpa using (continuous_sub_right t₀).tendsto t₀
  have hEv'' : ∀ᶠ t in 𝓝 t₀, GoodLoopChain (L (t - t₀)) (D (t - t₀)) :=
    htend.eventually hEv'
  refine hEv''.mono fun t ht => ?_
  have hsub : t₀ + (t - t₀) = t := by abel
  have hLt : L (t - t₀) = coreLoop (blockChart (fun s p => chartPert s p) Q u
      (fun j => blk j t) k) := by
    funext s
    simp only [hLdef]
    rw [hsub]
  have hDt : D (t - t₀) = clampedSweep (cblk (k + 1)) (fun r => 1 - r)
      (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t) (k + 1)) := by
    funext x
    simp only [hDdef]
    rw [hsub]
  rwa [hLt, hDt] at ht

end

end Work.Drive
