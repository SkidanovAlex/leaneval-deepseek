import Mathlib
import Submission.Work.Drive.tripleChartCapping
import Submission.Work.Drive.sweepGenericity
import Submission.Work.Drive.fderiv_halfLine_clampedSweep
import Submission.Work.Drive.tripleTransverseE_prod_equiv

/-!
# The transversality of three radial sweeps, in the manifold sense

This is the last link of the genericity lane: it composes the chart ladder

* `Work.Drive.tripleTransverse_mfderiv_iff_fderiv_chartAt_self` (the condition is chart-local),
* `Work.Drive.fderiv_chartAt_cappingCharted` (the chart of `Y` is that of `(0,∞) × ℝP³`),
* `Work.Drive.fderiv_chartAt_halfLine_clampedSweep_chartAt` (the chart derivative is
  `psiEquiv ∘ (logEucl ∘ level block, class block)`),
* `Work.Drive.tripleTransverseE_comp_of_equiv` and
  `Work.Drive.tripleTransverseE_prod_comp_continuousLinearEquiv` (the two isomorphisms may be dropped),

with the block-level criterion `Work.Drive.tripleTransverseE_clampedSweeps`, so that the manifold
transversality of three radial sweeps at a triple point follows from the two conditions on the
**planes** (radial coefficients non-zero, three class `2`-planes in general position).
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

set_option maxHeartbeats 8000000

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

theorem tripleTransverse_clampedSweeps
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (ind : Fin 3 → Fin 4)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hpt : ∀ k, Work.Drive.clampedSweep (c k) ψ (P k) (x k)
      = Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0))
    (hchart2 : ∀ k, (@chartAt (EuclideanSpace ℝ (Fin 3)) _
        (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
        (Work.Drive.projCharted 3) (Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2 :
        OpenPartialHomeomorph (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
          (EuclideanSpace ℝ (Fin 3)))
      = Work.Drive.projChart (ind k))
    (hrc : ∀ k, ContinuousAt (fun u => (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep (c k) ψ (P k) u)).1) (x k))
    (hrd : ∀ k, DifferentiableAt ℝ (fun u => Real.log
      ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep (c k) ψ (P k) u)).1 : ℝ)) (x k))
    (hz : ∀ k, (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).1 ∈
        (@chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0:ℝ)) _
          (Homeomorph.chartedSpace Work.Drive.expHomeo)
          (Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).1).source)
    (h₁ : ∀ k, DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 1)) _
          (Set.Ioi (0:ℝ)) _ (Homeomorph.chartedSpace Work.Drive.expHomeo)
          (Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).1
          ((Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c k) ψ (P k) u)).1)) (x k))
    (h₂ : ∀ k, DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 3)) _
          (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ (Work.Drive.projCharted 3)
          (Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2
          ((Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c k) ψ (P k) u)).2)) (x k))
    (hlog : ∀ k, ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) Work.Drive.Ctop
        (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P k y)))
        (Work.Drive.mk2 (x k 0) (x k 1)))
    (hF : ∀ k, DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.projChartMap (ind k) ((Work.Drive.cappingSpaceHomeoProj (P k y)).2))
        (Work.Drive.mk2 (x k 0) (x k 1)))
    (ha : ∀ k, deriv ψ (x k 2) * (Real.log (c k)
        - Real.log (Work.Drive.levelOf (P k (Work.Drive.mk2 (x k 0) (x k 1))))) ≠ 0)
    (hc : ∀ k, Function.Injective (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.projChartMap (ind k) ((Work.Drive.cappingSpaceHomeoProj (P k y)).2))
        (Work.Drive.mk2 (x k 0) (x k 1))))
    (hV : (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap (ind 0) ((Work.Drive.cappingSpaceHomeoProj (P 0 y)).2))
          (Work.Drive.mk2 (x 0 0) (x 0 1))).range ⊓
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap (ind 1) ((Work.Drive.cappingSpaceHomeoProj (P 1 y)).2))
          (Work.Drive.mk2 (x 1 0) (x 1 1))).range ⊓
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap (ind 2) ((Work.Drive.cappingSpaceHomeoProj (P 2 y)).2))
          (Work.Drive.mk2 (x 2 0) (x 2 1))).range = ⊥) :
    TripleTransverse
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 0) ψ (P 0)) (x 0))
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 1) ψ (P 1)) (x 1))
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 2) ψ (P 2)) (x 2)) := by
  have hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Work.Drive.Ctop
      (Work.Drive.clampedSweep (c k) ψ (P k)) :=
    fun k => contMDiff_clampedSweep (c k) ψ (P k) hψ (hP k)
  have hcont : ∀ k, ContinuousAt (Work.Drive.clampedSweep (c k) ψ (P k)) (x k) :=
    fun k => (hD k).continuous.continuousAt
  refine (tripleTransverse_mfderiv_iff_fderiv_chartAt_self _ hD x (hpt 1).symm (hpt 2).symm).mpr ?_
  set p0 : Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)) with hp0
  have hz0 : ∀ k, (Work.Drive.clampedSweep (c k) ψ (P k) (x k))
      ∈ (chartAt (EuclideanSpace ℝ (Fin 4))
          (Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0))).source := by
    intro k
    rw [hpt k]
    exact mem_chart_source _ _
  have g : ∀ k, fderiv ℝ (fun u => chartAt (EuclideanSpace ℝ (Fin 4))
        (Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0))
        (Work.Drive.clampedSweep (c k) ψ (P k) u)) (x k)
      = fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
          (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
          Work.Drive.halfLineProjectiveCharted p0
          (Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep (c k) ψ (P k) u))) (x k) :=
    fun k => fderiv_chartAt_cappingCharted (Work.Drive.clampedSweep (c k) ψ (P k)) (x k)
      (Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)) (hcont k) (hz0 k)
  rw [g 0, g 1, g 2]
  have q1 : ∀ k, (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).1 = p0.1 := fun k => by rw [hpt k, hp0]
  have q2 : ∀ k, (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2 = p0.2 := fun k => by rw [hpt k, hp0]
  have hch : ∀ k, (@chartAt (EuclideanSpace ℝ (Fin 3)) _
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
      (Work.Drive.projCharted 3) p0.2 :
      OpenPartialHomeomorph (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
        (EuclideanSpace ℝ (Fin 3))) = Work.Drive.projChart (ind k) := by
    intro k
    rw [← q2 k]
    exact hchart2 k
  have hzq : ∀ k, (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).1 ∈
      (@chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0:ℝ)) _
        (Homeomorph.chartedSpace Work.Drive.expHomeo) p0.1).source := fun k => by
    simpa only [q1 k] using hz k
  have h₁q : ∀ k, DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 1)) _
      (Set.Ioi (0:ℝ)) _ (Homeomorph.chartedSpace Work.Drive.expHomeo) p0.1
      ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep (c k) ψ (P k) u)).1)) (x k) :=
    fun k => by rw [← q1 k]; exact h₁ k
  have h₂q : ∀ k, DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 3)) _
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ (Work.Drive.projCharted 3) p0.2
      ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep (c k) ψ (P k) u)).2)) (x k) :=
    fun k => by rw [← q2 k]; exact h₂ k
  have hbl : ∀ k, fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
        (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
        Work.Drive.halfLineProjectiveCharted p0
        (Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep (c k) ψ (P k) u))) (x k)
      = (Work.Drive.psiEquiv : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
          EuclideanSpace ℝ (Fin 4)).comp
        ((Work.Drive.logEucl.comp (fderiv ℝ (fun u => Real.log
            (Work.Drive.levelOf (Work.Drive.clampedSweep (c k) ψ (P k) u))) (x k))).prod
          (fderiv ℝ (fun u => Work.Drive.projChartMap (ind k)
            ((Work.Drive.cappingSpaceHomeoProj
              (Work.Drive.clampedSweep (c k) ψ (P k) u)).2)) (x k))) :=
    fun k => fderiv_chartAt_halfLine_clampedSweep_chartAt (c k) ψ (P k) (ind k) p0 (x k)
      (q1 k) (q2 k) (hch k) (hrc k) (hrd k) (hzq k) (h₁q k) (h₂q k)
  rw [hbl 0, hbl 1, hbl 2]
  refine (tripleTransverseE_comp_of_equiv
    (E := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))
    Work.Drive.psiEquiv _ _ _).mpr ?_
  refine (tripleTransverseE_prod_comp_continuousLinearEquiv
    (E := ℝ) (E' := EuclideanSpace ℝ (Fin 1)) (G := EuclideanSpace ℝ (Fin 3))
    Work.Drive.logEuclEquiv
    (fun k => fderiv ℝ (fun u => Real.log
      (Work.Drive.levelOf (Work.Drive.clampedSweep (c k) ψ (P k) u))) (x k))
    (fun k => fderiv ℝ (fun u => Work.Drive.projChartMap (ind k)
      ((Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) u)).2)) (x k))).mpr ?_
  exact tripleTransverseE_clampedSweeps c ψ P ind hψ x hlog hF ha hc hV

end

end Work.Drive
