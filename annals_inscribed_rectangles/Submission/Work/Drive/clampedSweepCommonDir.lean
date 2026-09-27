import Mathlib
import Submission.Work.Drive.sweepTransversalityContMDiff
import Submission.Work.Drive.fderiv_log_levelOf_clampedSweep
import Submission.Work.Drive.fderiv_projChartMap_snd_clampedSweep_apply
import Submission.Work.Drive.projChartIndexOf

/-!
# The common tangent direction of three radial sweeps is the radial direction

At a triple point `x` of three radial sweeps `D k = clampedSweep (c k) ψ (P k)`, the tangent direction
of the triple intersection is, in the parameters `x k`, the *radial* direction `e₂ = ∂/∂(x k 2)` —
rescaled in each factor so that the three image vectors agree: all three derivative images contain the
same radial line (`GENERICITY_INTERFACE_STATUS.md` §3), and the coefficients are the radial
coefficients `A k = deriv ψ (x k 2) · (log (c k) − log r k)` of `Work.Drive.fderiv_log_levelOf_clampedSweep`.

Concretely `TripleCommonDir (mfderiv D k (x k)) (fun k => (1 / A k) • e₂)`, which is the `v`-part of
the `face` field of `Work.Drive.Meet3Generic`.  The computation is: the chart derivative of the sweep
(`fderiv_chartAt_clampedSweep_self`) in the direction `e₂` is `psiEquiv (logEucl (A k), 0)`, because
the level block is `A k` (`fderiv_log_levelOf_clampedSweep`) and the class block vanishes
(`fderiv_projChartMap_snd_clampedSweep_apply_single`); normalising by `1 / A k` makes all three equal
to the fixed vector `psiEquiv (logEucl 1, 0)`.

The file also provides

* `Work.Drive.fderiv_chartAt_clampedSweep_self` — the chart derivative of a radial sweep in block
  form, with **all** differentiability side conditions discharged from `ContMDiff (P)` (the reusable
  form of the auxiliary block of `sweepTransversalityContMDiff.lean`),
* `Work.Drive.differentiableAt_projChartMap_cls_of_contMDiff` — the class component of a smooth map
  into the capping space is chart-differentiable.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold Topology Filter

noncomputable section

set_option maxHeartbeats 8000000

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

/-- **The class component of a smooth map into the capping space is chart-differentiable**, in any
projective chart valid at the class of its value. -/
theorem differentiableAt_projChartMap_cls_of_contMDiff
    {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) → Work.Drive.CappingSpace)
    (hQ : ContMDiff (𝓡 n) (𝓡 4) Work.Drive.Ctop Q) (z : EuclideanSpace ℝ (Fin n)) (i : Fin 4)
    (hzi : (Work.Drive.cappingSpaceHomeoProj (Q z)).2 ∈ Work.Drive.projChartSource i) :
    DifferentiableAt ℝ (fun y => Work.Drive.projChartMap i
      ((Work.Drive.cappingSpaceHomeoProj (Q y)).2)) z := by
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

/-- **The chart derivative of a radial sweep, in block form, from smoothness of the plane alone.**  This
is `Work.Drive.fderiv_chartAt_halfLine_clampedSweep` with every differentiability side condition
discharged from `ContMDiff (𝓡 2) (𝓡 4) Ctop P`, and the chart of the capping space identified with the
chart of `(0,∞) × ℝP³` along `Work.Drive.cappingSpaceHomeoProj`.
-/
theorem fderiv_chartAt_clampedSweep_self
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop P)
    (ind : Fin 4) (x : EuclideanSpace ℝ (Fin 3))
    (hchart2 : (@chartAt (EuclideanSpace ℝ (Fin 3)) _
        (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
        (Work.Drive.projCharted 3) (Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.clampedSweep c ψ P x)).2 :
        OpenPartialHomeomorph (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
          (EuclideanSpace ℝ (Fin 3)))
      = Work.Drive.projChart ind) :
    fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _ Work.Drive.CappingSpace _
        Work.Drive.cappingCharted (Work.Drive.clampedSweep c ψ P x)
        (Work.Drive.clampedSweep c ψ P u)) x
      = (Work.Drive.psiEquiv : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) →L[ℝ]
            EuclideanSpace ℝ (Fin 4)).comp
        ((Work.Drive.logEucl.comp (fderiv ℝ (fun u => Real.log
              (Work.Drive.levelOf (Work.Drive.clampedSweep c ψ P u))) x)).prod
          (fderiv ℝ (fun u => Work.Drive.projChartMap ind
              ((Work.Drive.cappingSpaceHomeoProj
                (Work.Drive.clampedSweep c ψ P u)).2)) x)) := by
  have hD : ContMDiff (𝓡 3) (𝓡 4) Work.Drive.Ctop
      (Work.Drive.clampedSweep c ψ P) :=
    Work.Drive.contMDiff_clampedSweep c ψ P hψ hP
  have hcont : ContinuousAt (Work.Drive.clampedSweep c ψ P) x :=
    hD.continuous.continuousAt
  -- the chart of `ℝP³` at the class of the sweep, and the class of the plane it comes from
  have hzS : (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep c ψ P x)).2 ∈ Work.Drive.projChartSource ind := by
    have hmem : (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep c ψ P x)).2 ∈
        (@chartAt (EuclideanSpace ℝ (Fin 3)) _
          (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
          (Work.Drive.projCharted 3) (Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep c ψ P x)).2).source :=
      @mem_chart_source (EuclideanSpace ℝ (Fin 3)) _
        _ _ (Work.Drive.projCharted 3) _
    rw [hchart2, Work.Drive.projChart_source] at hmem
    exact hmem
  have hclsDiff : DifferentiableAt ℝ (fun u => Work.Drive.projChartMap ind
      ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep c ψ P u)).2)) x :=
    differentiableAt_projChartMap_cls_of_contMDiff _ hD x ind hzS
  have hrc : ContinuousAt (fun u => (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep c ψ P u)).1) x :=
    (Work.Drive.cappingSpaceHomeoProj.continuous.continuousAt.comp hcont).fst
  have hrd : DifferentiableAt ℝ (fun u => Real.log
      ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep c ψ P u)).1 : ℝ)) x :=
    (contMDiffAt_iff_contDiffAt.mp (Work.Drive.contMDiffAt_log_levelOf
      (Work.Drive.clampedSweep c ψ P) x hD.contMDiffAt)).differentiableAt (by norm_num)
  have hz : (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep c ψ P x)).1 ∈
      (@chartAt (EuclideanSpace ℝ (Fin 1)) _ (Set.Ioi (0:ℝ)) _
        (Homeomorph.chartedSpace Work.Drive.expHomeo) (Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.clampedSweep c ψ P x)).1).source :=
    @mem_chart_source (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ)) _ _
      (Homeomorph.chartedSpace Work.Drive.expHomeo) _
  have h₁ : DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 1)) _
      (Set.Ioi (0:ℝ)) _ (Homeomorph.chartedSpace Work.Drive.expHomeo)
      (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep c ψ P x)).1
      ((Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep c ψ P u)).1)) x := by
    rw [(Work.Drive.eventuallyEq_chartAt_expHomeo
      (fun u => (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep c ψ P u)).1) x
      (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep c ψ P x)).1 hrc hz).differentiableAt_iff]
    exact Work.Drive.logEucl.differentiableAt.comp x hrd
  have h₂ : DifferentiableAt ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 3)) _
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ (Work.Drive.projCharted 3)
      (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep c ψ P x)).2
      ((Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep c ψ P u)).2)) x := by
    have heq : (fun u => @chartAt (EuclideanSpace ℝ (Fin 3)) _
        (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ (Work.Drive.projCharted 3)
        (Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.clampedSweep c ψ P x)).2
        ((Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.clampedSweep c ψ P u)).2))
        = (fun u => Work.Drive.projChartMap ind
          ((Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep c ψ P u)).2)) := by
      funext u
      rw [hchart2, Work.Drive.projChart_apply]
    rw [heq]
    exact hclsDiff
  rw [Work.Drive.fderiv_chartAt_cappingCharted (Work.Drive.clampedSweep c ψ P) x
      (Work.Drive.clampedSweep c ψ P x) hcont
      (@mem_chart_source (EuclideanSpace ℝ (Fin 4)) Work.Drive.CappingSpace _ _
        Work.Drive.cappingCharted _),
    Work.Drive.fderiv_chartAt_halfLine_clampedSweep c ψ P ind x hchart2 hrc hrd hz h₁ h₂]

/-- **The derivative of the charted radial sweep along the radial direction.**  The value is
`psiEquiv (logEucl A, 0)` with `A` the radial coefficient. -/
theorem fderiv_chartAt_clampedSweep_self_smul_single_two
    (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop P)
    (ind : Fin 4) (x : EuclideanSpace ℝ (Fin 3))
    (hchart2 : (@chartAt (EuclideanSpace ℝ (Fin 3)) _
        (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
        (Work.Drive.projCharted 3) (Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.clampedSweep c ψ P x)).2 :
        OpenPartialHomeomorph (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
          (EuclideanSpace ℝ (Fin 3)))
      = Work.Drive.projChart ind)
    (lam : ℝ) :
    fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _ Work.Drive.CappingSpace _
        Work.Drive.cappingCharted (Work.Drive.clampedSweep c ψ P x)
        (Work.Drive.clampedSweep c ψ P u)) x
        (lam • EuclideanSpace.single 2 (1 : ℝ))
      = lam • Work.Drive.psiEquiv (Work.Drive.logEucl (deriv ψ (x 2) * (Real.log c
          - Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0) (x 1)))))), 0) := by
  have hD : ContMDiff (𝓡 3) (𝓡 4) Work.Drive.Ctop
      (Work.Drive.clampedSweep c ψ P) :=
    Work.Drive.contMDiff_clampedSweep c ψ P hψ hP
  have hzS : (Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep c ψ P x)).2 ∈ Work.Drive.projChartSource ind := by
    have hmem : (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep c ψ P x)).2 ∈
        (@chartAt (EuclideanSpace ℝ (Fin 3)) _
          (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
          (Work.Drive.projCharted 3) (Work.Drive.cappingSpaceHomeoProj
            (Work.Drive.clampedSweep c ψ P x)).2).source :=
      @mem_chart_source (EuclideanSpace ℝ (Fin 3)) _
        _ _ (Work.Drive.projCharted 3) _
    rw [hchart2, Work.Drive.projChart_source] at hmem
    exact hmem
  have hclsDiff : DifferentiableAt ℝ (fun u => Work.Drive.projChartMap ind
      ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep c ψ P u)).2)) x :=
    differentiableAt_projChartMap_cls_of_contMDiff _ hD x ind hzS
  have hlog : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) Work.Drive.Ctop
      (fun y : EuclideanSpace ℝ (Fin 2) => Real.log (Work.Drive.levelOf (P y)))
      (Work.Drive.mk2 (x 0) (x 1)) :=
    Work.Drive.contMDiffAt_log_levelOf P (Work.Drive.mk2 (x 0) (x 1)) hP.contMDiffAt
  have hLe : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) => Real.log
      (Work.Drive.levelOf (Work.Drive.clampedSweep c ψ P u))) x
      (EuclideanSpace.single 2 (1 : ℝ))
      = deriv ψ (x 2) * (Real.log c
        - Real.log (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0) (x 1))))) :=
    Work.Drive.fderiv_log_levelOf_clampedSweep c ψ P hψ x hlog
  have hCe : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) => Work.Drive.projChartMap ind
      ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep c ψ P u)).2)) x
      (EuclideanSpace.single 2 (1 : ℝ)) = 0 :=
    Work.Drive.fderiv_projChartMap_snd_clampedSweep_apply_single c ψ P ind x hclsDiff
  rw [fderiv_chartAt_clampedSweep_self c ψ P hψ hP ind x hchart2]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  have hcomp : Work.Drive.logEucl ((fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) => Real.log
        (Work.Drive.levelOf (Work.Drive.clampedSweep c ψ P u))) x)
        (lam • EuclideanSpace.single 2 (1 : ℝ)))
      = Work.Drive.logEucl (lam * (deriv ψ (x 2) * (Real.log c - Real.log
          (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0) (x 1))))))) := by
    rw [ContinuousLinearMap.map_smul, hLe, smul_eq_mul]
  have hcomp2 : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin 3) => Work.Drive.projChartMap ind
        ((Work.Drive.cappingSpaceHomeoProj (Work.Drive.clampedSweep c ψ P u)).2)) x)
        (lam • EuclideanSpace.single 2 (1 : ℝ)) = 0 := by
    rw [ContinuousLinearMap.map_smul, hCe, smul_zero]
  rw [hcomp, hcomp2]
  have h1 : Work.Drive.logEucl (lam * (deriv ψ (x 2) * (Real.log c - Real.log
        (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0) (x 1)))))))
      = lam • Work.Drive.logEucl (deriv ψ (x 2) * (Real.log c - Real.log
          (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0) (x 1)))))) := by
    rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul]
  have h2 := ContinuousLinearMap.map_smul (Work.Drive.psiEquiv :
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) →L[ℝ] EuclideanSpace ℝ (Fin 4))
      lam (Work.Drive.logEucl (deriv ψ (x 2) * (Real.log c - Real.log
        (Work.Drive.levelOf (P (Work.Drive.mk2 (x 0) (x 1)))))), (0 : EuclideanSpace ℝ (Fin 3)))
  rw [Prod.smul_mk, smul_zero] at h2
  rw [h1, h2]
  rfl

/-- **The common tangent direction of three radial sweeps is the radial direction**, rescaled by the
radial coefficients: `TripleCommonDir (mfderiv D k (x k)) (fun k => (1 / A k) • e₂)`.  The three
`A k` are the radial coefficients; the hypothesis `hA` records their value, `hA0` that they are
non-zero. -/
theorem tripleCommonDir_clampedSweeps
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hpt : ∀ k, Work.Drive.clampedSweep (c k) ψ (P k) (x k)
      = Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0))
    (A : Fin 3 → ℝ)
    (hA : ∀ k, A k = deriv ψ (x k 2) * (Real.log (c k) - Real.log
      (Work.Drive.levelOf (P k (Work.Drive.mk2 (x k 0) (x k 1))))))
    (hA0 : ∀ k, A k ≠ 0) :
    TripleCommonDir
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 0) ψ (P 0)) (x 0))
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 1) ψ (P 1)) (x 1))
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 2) ψ (P 2)) (x 2))
      (fun k => (1 / A k) • EuclideanSpace.single 2 (1 : ℝ)) := by
  have hDsm : ∀ k, ContMDiff (𝓡 3) (𝓡 4) Work.Drive.Ctop
      (Work.Drive.clampedSweep (c k) ψ (P k)) :=
    fun k => Work.Drive.contMDiff_clampedSweep (c k) ψ (P k) hψ (hP k)
  have hval : ∀ k, fderiv ℝ (fun u => @chartAt (EuclideanSpace ℝ (Fin 4)) _
      Work.Drive.CappingSpace _ Work.Drive.cappingCharted
      (Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0))
      (Work.Drive.clampedSweep (c k) ψ (P k) u)) (x k)
        ((1 / A k) • EuclideanSpace.single 2 (1 : ℝ))
      = Work.Drive.psiEquiv (Work.Drive.logEucl 1, 0) := by
    intro k
    rw [← hpt k]
    have hstep := fderiv_chartAt_clampedSweep_self_smul_single_two (c k) ψ (P k) hψ (hP k)
      (Work.Drive.projChartIndexOf (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2) (x k)
      (Work.Drive.projCharted_chartAt_eq_projChart _) (1 / A k)
    rw [hstep, ← hA k]
    rw [← ContinuousLinearEquiv.map_smul, Prod.smul_mk, smul_zero,
      ← ContinuousLinearMap.map_smul, smul_eq_mul, one_div, inv_mul_cancel₀ (hA0 k)]
  refine (Work.Drive.tripleCommonDir_mfderiv_iff_fderiv_chartAt_self
    (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) hDsm x (hpt 1).symm (hpt 2).symm
    (fun k => (1 / A k) • EuclideanSpace.single 2 (1 : ℝ))).mpr ?_
  constructor
  · rw [hval 0, hval 1]
  · rw [hval 0, hval 2]

end

end Work.Drive
