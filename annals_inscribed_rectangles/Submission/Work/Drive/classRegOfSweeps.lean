import Mathlib
import Submission.Work.Drive.classLevelTransverse
import Submission.Work.Drive.sweepTransversalityContMDiff
import Submission.Work.Drive.blocksCLM
import Submission.Work.Drive.tripleTransverseE_prod_equiv

/-!
# The regularity of the plane class maps from the transversality of the sweeps

`Work.Drive.tripleTransverse_clampedSweeps_of_contMDiff` derives the manifold transversality of three
radial sweeps from the *class* conditions `hc`/`hV` on the planes (plus the radial coefficients `ha`).
This file proves the **converse** extraction, which is what the ends clause needs: from the
transversality of the three sweeps at a triple point, the three plane **class** derivatives are
injective and their `2`-planes meet in `⊥`.

The mechanism is `Work.Drive.inj_inf_of_tripleTransverseE_of_blocks` applied to the *block form* of the
charted sweep derivatives
(`Work.Drive.fderiv_log_levelOf_clampedSweep_eq`, `Work.Drive.fderiv_projChartMap_snd_clampedSweep_eq`):
the class block of the charted derivative of a sweep is `(plane class derivative) ∘ mk2CLM`, and the
general position of the blocks is `TripleTransverse` transported into the chart.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold Topology Filter

noncomputable section

set_option maxHeartbeats 8000000

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

theorem classReg_of_sweepTransverse
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
    (hF : ∀ k, DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.projChartMap (ind k) ((Work.Drive.cappingSpaceHomeoProj (P k y)).2))
        (Work.Drive.mk2 (x k 0) (x k 1)))
    (h : TripleTransverse
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 0) ψ (P 0)) (x 0))
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 1) ψ (P 1)) (x 1))
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 2) ψ (P 2)) (x 2))) :
    (∀ k, Function.Injective (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.projChartMap (ind k) ((Work.Drive.cappingSpaceHomeoProj (P k y)).2))
        (Work.Drive.mk2 (x k 0) (x k 1)))) ∧
      ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap (ind 0) ((Work.Drive.cappingSpaceHomeoProj (P 0 y)).2))
          (Work.Drive.mk2 (x 0 0) (x 0 1))).range ⊓
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap (ind 1) ((Work.Drive.cappingSpaceHomeoProj (P 1 y)).2))
          (Work.Drive.mk2 (x 1 0) (x 1 1))).range ⊓
        (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap (ind 2) ((Work.Drive.cappingSpaceHomeoProj (P 2 y)).2))
          (Work.Drive.mk2 (x 2 0) (x 2 1))).range = ⊥) := by
  have hD : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Work.Drive.Ctop
      (Work.Drive.clampedSweep (c k) ψ (P k)) :=
    fun k => contMDiff_clampedSweep (c k) ψ (P k) hψ (hP k)
  have hcont : ∀ k, ContinuousAt (Work.Drive.clampedSweep (c k) ψ (P k)) (x k) :=
    fun k => (hD k).continuous.continuousAt
  -- ### 1. the condition is chart-local at the (common) value
  have hraw := (tripleTransverse_mfderiv_iff_fderiv_chartAt_self
    (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) hD x (hpt 1).symm (hpt 2).symm).mp h
  -- ### 2. the chart of `CappingSpace` is the chart of `(0,∞) × ℝP³`
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
  rw [g 0, g 1, g 2] at hraw
  -- ### 3. the charted derivative of a sweep, in the `(0,∞) × ℝP³` coordinates
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
  -- ### the auxiliary differentiability data, from smoothness of the planes
  have hrc : ∀ k, ContinuousAt (fun u => (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep (c k) ψ (P k) u)).1) (x k) := by
    intro k
    have h1 : ContinuousAt (fun u => Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) u)) (x k) :=
      Work.Drive.cappingSpaceHomeoProj.continuous.continuousAt.comp ((hD k).continuous.continuousAt)
    exact h1.fst
  have hrd : ∀ k, DifferentiableAt ℝ (fun u => Real.log
      ((Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) u)).1 : ℝ)) (x k) := by
    intro k
    have h := Work.Drive.contMDiffAt_log_levelOf (Work.Drive.clampedSweep (c k) ψ (P k))
      (x k) ((hD k).contMDiffAt)
    exact (contMDiffAt_iff_contDiffAt.mp h).differentiableAt (by norm_num)
  have hz : ∀ k, (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).1 ∈
      (@chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0:ℝ)) _
        (Homeomorph.chartedSpace Work.Drive.expHomeo) (Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).1).source := by
    intro k
    exact @mem_chart_source (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ)) _ _
      (Homeomorph.chartedSpace Work.Drive.expHomeo) _
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
      ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep (c k) ψ (P k) u)).2)) (x k) := by
    intro k
    have heq : (fun u => @chartAt (EuclideanSpace ℝ (Fin 3)) _
        (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ (Work.Drive.projCharted 3) p0.2
        ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep (c k) ψ (P k) u)).2))
        = (fun u => Work.Drive.projChartMap (ind k)
          ((Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep (c k) ψ (P k) u)).2)) := by
      funext u
      rw [hch k, Work.Drive.projChart_apply]
    rw [heq]
    exact hclass (Work.Drive.clampedSweep (c k) ψ (P k)) (hD k) (x k) (ind k) (hzS k)
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
  rw [hbl 0, hbl 1, hbl 2] at hraw
  -- ### 4. drop the two isomorphisms
  have hblk := (tripleTransverseE_comp_of_equiv
    (E := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))
    Work.Drive.psiEquiv _ _ _).mp hraw
  have hblk2 := (tripleTransverseE_prod_comp_continuousLinearEquiv
    (E := ℝ) (E' := EuclideanSpace ℝ (Fin 1)) (G := EuclideanSpace ℝ (Fin 3))
    Work.Drive.logEuclEquiv
    (fun k => fderiv ℝ (fun u => Real.log
      (Work.Drive.levelOf (Work.Drive.clampedSweep (c k) ψ (P k) u))) (x k))
    (fun k => fderiv ℝ (fun u => Work.Drive.projChartMap (ind k)
      ((Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) u)).2)) (x k))).mp hblk
  -- ### 5. the class block of the charted derivative is `(plane class derivative) ∘ mk2CLM`
  have hf : ∀ k (v : EuclideanSpace ℝ (Fin 3)),
      ((((fderiv ℝ (fun u => Real.log
            (Work.Drive.levelOf (Work.Drive.clampedSweep (c k) ψ (P k) u))) (x k)).prod
          (fderiv ℝ (fun u => Work.Drive.projChartMap (ind k)
            ((Work.Drive.cappingSpaceHomeoProj
              (Work.Drive.clampedSweep (c k) ψ (P k) u)).2)) (x k))) v)).2
      = (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap (ind k) ((Work.Drive.cappingSpaceHomeoProj (P k y)).2))
          (Work.Drive.mk2 (x k 0) (x k 1))) (Work.Drive.mk2CLM v) := by
    intro k v
    have hC := fderiv_projChartMap_snd_clampedSweep_eq (c k) ψ (P k) (ind k) (x k) (hF k)
    exact congrFun (congrArg DFunLike.coe hC) v
  have hmain :
      (∀ k, Function.Injective (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
          Work.Drive.projChartMap (ind k) ((Work.Drive.cappingSpaceHomeoProj (P k y)).2))
          (Work.Drive.mk2 (x k 0) (x k 1)))) ∧
        ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
            Work.Drive.projChartMap (ind 0) ((Work.Drive.cappingSpaceHomeoProj (P 0 y)).2))
            (Work.Drive.mk2 (x 0 0) (x 0 1))).range ⊓
          (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
            Work.Drive.projChartMap (ind 1) ((Work.Drive.cappingSpaceHomeoProj (P 1 y)).2))
            (Work.Drive.mk2 (x 1 0) (x 1 1))).range ⊓
          (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
            Work.Drive.projChartMap (ind 2) ((Work.Drive.cappingSpaceHomeoProj (P 2 y)).2))
            (Work.Drive.mk2 (x 2 0) (x 2 1))).range = ⊥) :=
    inj_inf_of_tripleTransverseE_of_blocks Work.Drive.mk2CLM
      (fun k => ((fderiv ℝ (fun u => Real.log
            (Work.Drive.levelOf (Work.Drive.clampedSweep (c k) ψ (P k) u))) (x k)).prod
          (fderiv ℝ (fun u => Work.Drive.projChartMap (ind k)
            ((Work.Drive.cappingSpaceHomeoProj
              (Work.Drive.clampedSweep (c k) ψ (P k) u)).2)) (x k))))
      (fun k => fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.projChartMap (ind k) ((Work.Drive.cappingSpaceHomeoProj (P k y)).2))
        (Work.Drive.mk2 (x k 0) (x k 1)))
      hf hblk2
  exact hmain

end

end Work.Drive
