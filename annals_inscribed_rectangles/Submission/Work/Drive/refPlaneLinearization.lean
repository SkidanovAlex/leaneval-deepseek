import Mathlib
import Submission.Work.Drive.refTripleProducerDefs
import Submission.Work.Drive.chartPert_linPlaneChart
import Submission.Work.Drive.pairRegLinBase
import Submission.Work.Drive.linPlaneChartsEndTripleReg

/-!
# The perturbed reference plane of the `hn2` reference triple is still a **linear** plane chart

Block `2` of the `hn2` reference triple is `chartPert τ ∘ refPlanePres φ lam hlam` where
`refPlanePres φ lam hlam = diskPlane (linPlaneChart (φ 2) lam hlam)` is the *linear* reference plane.
`Work.Drive.chartPert_linPlaneChart` (`Drive/chartPert_linPlaneChart.lean`, proved) says that the chart
perturbation of a linear plane chart is again a linear plane chart, with the functional transported by
`classEquiv τ` and the level scaled by `levelScale τ`:

> `chartPert τ ∘ linPlaneChart φ lam hlam = linPlaneChart (φ.trans (classEquiv τ)) (levelScale τ lam) …`

Consequently the two rows of `hasClassLinearization_of_endData` that pair the hn2 reference triple's
*linear* reference plane with the two linear charts — `hpairL0P2` (`PairReg lin₀ P̂₂`) and `hendL10P2`
(`EndTripleReg lin₁ lin₀ P̂₂`) — are, **at every parameter `t`**, statements about *three linear plane
charts*: `φ 0`, `φ 1` (or `φ 2`) and `(φ 2).trans (classEquiv (blk 2 t))`.  Hence they can be discharged
by the linear machinery of `Drive/linShearIncidence.lean` / `Drive/pairRegLinBase.lean` /
`Drive/linPlaneChartsEndTripleReg.lean` (the criterion `pairReg_linPlaneCharts_of_incidence` and the row
`endTripleReg_linPlaneCharts_uncond`) — no `LoopBoxData`, no `Meet3Hyp` and no Sard call is needed for
these two rows; what remains is the *plane* general position of the transported plane
`(φ 2).trans (classEquiv (blk 2 t))`, an open (algebraic) condition in `t`.  See
`REFPLANE_LINEARIZATION.md`.

(The row `hendL012`, `EndTripleReg lin₀ P̂₁ P̂₂`, is *not* of this form: its middle block
`P̂₁ = chartPert τ₁ ∘ rotPresentation Q u` is a perturbed *rotated chart* of the curve's chart `Q`, not a
linear plane.)
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The perturbation of the reference plane presentation is a linear plane chart.** -/
theorem chartPert_refPlanePres_eq (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (τ : Eucl 3) :
    (fun y : EuclideanSpace ℝ (Fin 2) => chartPert τ (refPlanePres φ lam hlam y))
      = diskPlane (linPlaneChart ((φ 2).trans (classEquiv τ))
          (((levelScale τ ⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))) : ℝ)
          (levelScale τ ⟨lam, hlam⟩).2) := by
  funext y
  simp only [refPlanePres, diskPlane_apply]
  exact congrFun (chartPert_linPlaneChart (φ 2) lam hlam τ) (sqDisk (foldBox y))

/-- **Block `2` of the `hn2` reference triple, linearised.** -/
theorem refBlock_two_eq_linPlaneChart (Q : ℂ → CappingSpace)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (u v : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) :
    refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2
      = diskPlane (linPlaneChart ((φ 2).trans (classEquiv (blk 2 t)))
          (((levelScale (blk 2 t) ⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))) : ℝ)
          (levelScale (blk 2 t) ⟨lam, hlam⟩).2) := by
  have h2 : refTriple Q (refPlanePres φ lam hlam) u v 2 = refPlanePres φ lam hlam := by
    simp [refTriple]
  funext y
  simp only [refBlock, h2]
  exact congrFun (chartPert_refPlanePres_eq φ lam hlam (blk 2 t)) y

/-- **The `hpairL0P2` row of the `hn2` reference triple is the linear criterion on the transported
plane.**  The six linear conditions of `pairReg_linPlaneCharts_of_incidence` for the pair
`(φ 0, (φ 2).trans (classEquiv (blk 2 t)))` give the row at every parameter `t`. -/
theorem pairReg_refBlock_two (Q : ℂ → CappingSpace)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (u v : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) (c : ℝ) (hc : 0 < c)
    (hl : linBdry (φ 0) ⊓ linBdry ((φ 2).trans (classEquiv (blk 2 t))) = ⊥)
    (h0 : ¬ linBdry (φ 0) ≤ linSub ((φ 2).trans (classEquiv (blk 2 t))))
    (h1 : ¬ linBdry ((φ 2).trans (classEquiv (blk 2 t))) ≤ linSub (φ 0))
    (hc0 : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      (φ 0) (linE0 + s • linE1) ∉ linSub ((φ 2).trans (classEquiv (blk 2 t))))
    (hc1 : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      ((φ 2).trans (classEquiv (blk 2 t))) (linE0 + s • linE1) ∉ linSub (φ 0))
    (hne : linSub (φ 0) ≠ linSub ((φ 2).trans (classEquiv (blk 2 t)))) :
    PairReg (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2)) := by
  have hstep := congrArg planeClassMap
    (refBlock_two_eq_linPlaneChart Q φ lam hlam u v t)
  rw [hstep]
  -- the class map of a linear plane chart does not depend on the level
  rw [← planeClassMap_diskPlane_linPlaneChart_eq_of_level ((φ 2).trans (classEquiv (blk 2 t)))
    c (((levelScale (blk 2 t) ⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))) : ℝ) hc
    (levelScale (blk 2 t) ⟨lam, hlam⟩).2]
  exact pairReg_linPlaneCharts_of_incidence (φ 0)
    ((φ 2).trans (classEquiv (blk 2 t))) c hc hl h0 h1 hc0 hc1 hne

/-- **The `hendL10P2` row of the `hn2` reference triple is the linear triple row on the transported
plane.**  With `Φ := ![φ 0, (φ 2).trans (classEquiv (blk 2 t)), φ 1]`, the general-position data
`hrank`/`hgen` of `endTripleReg_linPlaneCharts_uncond` give
`EndTripleReg (φ 1-chart) (φ 0-chart) (refBlock … t 2)`. -/
theorem endTripleReg_refBlock_two (Q : ℂ → CappingSpace)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (u v : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) (c : ℝ) (hc : 0 < c)
    (hrank : Module.finrank ℝ
      ↥(⨅ k : Fin 3, linSub ((![φ 0, (φ 2).trans (classEquiv (blk 2 t)), φ 1] : Fin 3 →
        Eucl 3 ≃L[ℝ] Eucl 3) k)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart ((![φ 0, (φ 2).trans (classEquiv (blk 2 t)), φ 1] : Fin 3 →
        Eucl 3 ≃L[ℝ] Eucl 3) k) c hc z
        ≠ linCommonPt (![φ 0, (φ 2).trans (classEquiv (blk 2 t)), φ 1] : Fin 3 →
          Eucl 3 ≃L[ℝ] Eucl 3) c hc hrank) :
    EndTripleReg (planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2)) := by
  have hstep := congrArg planeClassMap
    (refBlock_two_eq_linPlaneChart Q φ lam hlam u v t)
  rw [hstep]
  rw [← planeClassMap_diskPlane_linPlaneChart_eq_of_level ((φ 2).trans (classEquiv (blk 2 t)))
    c (((levelScale (blk 2 t) ⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))) : ℝ) hc
    (levelScale (blk 2 t) ⟨lam, hlam⟩).2]
  exact endTripleReg_linPlaneCharts_uncond
    (![φ 0, (φ 2).trans (classEquiv (blk 2 t)), φ 1] : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) c hc hrank hgen

end

end Work.Drive
