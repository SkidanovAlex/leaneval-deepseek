import Mathlib
import Submission.Work.Drive.sweepTransversality
import Submission.Work.Drive.contMDiffAt_projCharted_iff

/-!
# The transversality of three radial sweeps, from smoothness of the planes alone

`Work.Drive.tripleTransverse_clampedSweeps` proves the manifold transversality of three radial sweeps
from the two conditions on the planes (non-zero radial coefficients, general position of the three
class `2`-planes) **plus** a block of auxiliary differentiability hypotheses about the charted
composites of the sweeps (`hrc`, `hrd`, `hz`, `h₁`, `h₂`, `hlog`, `hF`).

This file discharges that block from `ContMDiff (𝓡 2) (𝓡 4) Ctop (P k)`, i.e. from smoothness of the
three **plane presentations** alone, using

* `Work.Drive.contMDiffAt_log_levelOf` (the logarithm of the radial coordinate is smooth),
* `Work.Drive.chartedStructure_contMDiffWithinAt` and
  `Work.Drive.contMDiffAt_halfLineProjective_iff` (smoothness into the capping space is smoothness of
  the two coordinates `(0,∞) × ℝP³`),
* `Work.Drive.contMDiffAt_projCharted_iff` (smoothness into `ℝP³` is smoothness of the concrete
  projective chart `projChartMap`),
* `Work.Drive.chartedStructure_contMDiffWithinAt` + `Work.Drive.eventuallyEq_chartAt_expHomeo`
  (the chart of `(0,∞)` is `logEucl ∘ log`).

The result is the statement actually usable by the geometric input: the transversality of the three
concrete sweeps of the plane presentation `P`, with **only** `hψ`, `hP`, the triple-point condition,
the three radial coefficients `ha` and the two geometric conditions `hc`, `hV` on the planes.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold Topology Filter

noncomputable section

set_option maxHeartbeats 8000000

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

theorem tripleTransverse_clampedSweeps_of_contMDiff
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
    fun k => Work.Drive.contMDiff_clampedSweep (c k) ψ (P k) hψ (hP k)
  -- ### the chart of the projective space at the class of the sweep is `projChart (ind k)`
  have hzS : ∀ k, (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2
      ∈ Work.Drive.projChartSource (ind k) := by
    intro k
    have hmem : (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2 ∈
        (@chartAt (EuclideanSpace ℝ (Fin 3)) _
          (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
          (Work.Drive.projCharted 3) (Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2).source :=
      @mem_chart_source (EuclideanSpace ℝ (Fin 3)) _
        _ _ (Work.Drive.projCharted 3) _
    rw [hchart2 k, Work.Drive.projChart_source] at hmem
    exact hmem
  -- ### the same for the plane itself (dilation does not change the class)
  have hzP : ∀ k, (Work.Drive.cappingSpaceHomeoProj
      (P k (Work.Drive.mk2 (x k 0) (x k 1)))).2 ∈ Work.Drive.projChartSource (ind k) := by
    intro k
    have hcl : (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2
        = (Work.Drive.cappingSpaceHomeoProj
            (P k (Work.Drive.mk2 (x k 0) (x k 1)))).2 := by
      rw [Work.Drive.clampedSweep_apply,
        Work.Drive.CapSmooth.cappingSpaceHomeoProj_scaleCapping]
    rw [← hcl]
    exact hzS k
  -- ### `hrc`
  have hrc : ∀ k, ContinuousAt (fun u => (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep (c k) ψ (P k) u)).1) (x k) := by
    intro k
    have h1 : ContinuousAt (fun u => Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) u)) (x k) :=
      Work.Drive.cappingSpaceHomeoProj.continuous.continuousAt.comp ((hD k).continuous.continuousAt)
    exact h1.fst
  -- ### `hrd`
  have hrd : ∀ k, DifferentiableAt ℝ (fun u => Real.log
      ((Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) u)).1 : ℝ)) (x k) := by
    intro k
    have h := Work.Drive.contMDiffAt_log_levelOf (Work.Drive.clampedSweep (c k) ψ (P k))
      (x k) ((hD k).contMDiffAt)
    exact (contMDiffAt_iff_contDiffAt.mp h).differentiableAt (by norm_num)
  -- ### `hz`
  have hz : ∀ k, (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).1 ∈
      (@chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0:ℝ)) _
        (Homeomorph.chartedSpace Work.Drive.expHomeo) (Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).1).source := by
    intro k
    exact @mem_chart_source (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ)) _ _
      (Homeomorph.chartedSpace Work.Drive.expHomeo) _
  -- ### `h₁`
  have h₁ : ∀ k, DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 1)) _
      (Set.Ioi (0:ℝ)) _ (Homeomorph.chartedSpace Work.Drive.expHomeo)
      (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).1
      ((Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) u)).1)) (x k) := by
    intro k
    rw [(Work.Drive.eventuallyEq_chartAt_expHomeo
      (fun u => (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) u)).1) (x k)
      (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).1 (hrc k) (hz k)).differentiableAt_iff]
    exact Work.Drive.logEucl.differentiableAt.comp (x k) (hrd k)
  -- ### the class component of a smooth map into the capping space is chart-differentiable
  have hclass : ∀ {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) → Work.Drive.CappingSpace),
      ContMDiff (𝓡 n) (𝓡 4) Work.Drive.Ctop Q → ∀ (z : EuclideanSpace ℝ (Fin n)) (i : Fin 4),
      (Work.Drive.cappingSpaceHomeoProj (Q z)).2 ∈ Work.Drive.projChartSource i →
      DifferentiableAt ℝ (fun y => Work.Drive.projChartMap i
        ((Work.Drive.cappingSpaceHomeoProj (Q y)).2)) z := by
    intro n Q hQ z i hzi
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
        (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
      Work.Drive.halfLineProjectiveCharted
    have hG : ContMDiffAt (𝓡 n) (𝓡 4) Work.Drive.Ctop
        (fun w => Work.Drive.cappingSpaceHomeoProj (Q w)) z := by
      have hiff := Work.Drive.chartedStructure_contMDiffWithinAt
        (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (E' := EuclideanSpace ℝ (Fin n)) (H' := EuclideanSpace ℝ (Fin n)) (𝓡 n)
        (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
        (M' := Work.Drive.CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
        Work.Drive.cappingSpaceHomeoProj.symm Q Set.univ z
      exact hiff.mp (hQ.contMDiffAt)
    obtain ⟨-, hcls⟩ := (Work.Drive.contMDiffAt_halfLineProjective_iff
      (fun w => Work.Drive.cappingSpaceHomeoProj (Q w)) z).mp hG
    have hF0 := ((Work.Drive.contMDiffAt_projCharted_iff
      (fun y => (Work.Drive.cappingSpaceHomeoProj (Q y)).2) z i hzi).mp hcls).2
    exact (contMDiffAt_iff_contDiffAt.mp hF0).differentiableAt (by norm_num)
  -- ### `hlog`
  have hlog : ∀ k, ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) Work.Drive.Ctop
      (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P k y)))
      (Work.Drive.mk2 (x k 0) (x k 1)) :=
    fun k => Work.Drive.contMDiffAt_log_levelOf (P k) (Work.Drive.mk2 (x k 0) (x k 1))
      ((hP k).contMDiffAt)
  -- ### `hF`
  have hF : ∀ k, DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
      Work.Drive.projChartMap (ind k) ((Work.Drive.cappingSpaceHomeoProj (P k y)).2))
      (Work.Drive.mk2 (x k 0) (x k 1)) :=
    fun k => hclass (P k) (hP k) _ (ind k) (hzP k)
  -- ### `h₂`
  have h₂ : ∀ k, DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 3)) _
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ (Work.Drive.projCharted 3)
      (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2
      ((Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) u)).2)) (x k) := by
    intro k
    have heq : (fun u => @chartAt (EuclideanSpace ℝ (Fin 3)) _
        (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ (Work.Drive.projCharted 3)
        (Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2
        ((Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.clampedSweep (c k) ψ (P k) u)).2))
        = (fun u => Work.Drive.projChartMap (ind k)
          ((Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c k) ψ (P k) u)).2)) := by
      funext u
      rw [hchart2 k, Work.Drive.projChart_apply]
    rw [heq]
    exact hclass (Work.Drive.clampedSweep (c k) ψ (P k)) (hD k) (x k) (ind k) (hzS k)
  exact Work.Drive.tripleTransverse_clampedSweeps c ψ P ind hψ hP x hpt hchart2
    hrc hrd hz h₁ h₂ hlog hF ha hc hV

end

end Work.Drive
