import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.refTripleClause
import Submission.Work.Drive.cappingCharted
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.blocksCLM

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold Filter Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted Work.Drive.t2Space_cappingSpace Work.Drive.projCharted
local instance : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) Work.Drive.Ctop (Projectivization ℝ (Work.Drive.Eucl 3)) := Work.Drive.isManifold_projCharted 3

noncomputable section

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- The transparent structure on `(0,∞)`, transported from `ℝ¹` along the exponential. -/
local instance clsSurjInstLine : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ)) :=
  Homeomorph.chartedSpace Work.Drive.expHomeo

/-- The transparent smooth structure on `(0,∞) × ℝP³`, modelled on `ℝ⁴`. -/
local instance clsSurjInstLineProjective : ChartedSpace (EuclideanSpace ℝ (Fin 4))
    (Set.Ioi (0:ℝ) × Projectivization ℝ (Work.Drive.Eucl 3)) :=
  Work.Drive.halfLineProjectiveCharted

/-- The source of the preferred chart of the transparent smooth structure on `(0,∞) × ℝP³`. -/
theorem clsSurj_source_chartAt_halfLine (q : Set.Ioi (0:ℝ) × Projectivization ℝ (Work.Drive.Eucl 3)) :
    (chartAt (EuclideanSpace ℝ (Fin 4)) q).source
      = (chartAt (EuclideanSpace ℝ (Fin 1)) q.1).source ×ˢ
        (chartAt (EuclideanSpace ℝ (Fin 3)) q.2).source := by
  have h1 : (chartAt (EuclideanSpace ℝ (Fin 4)) q)
      = (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3))) q).trans
          (Work.Drive.psiEquiv.toHomeomorph).toOpenPartialHomeomorph := rfl
  rw [h1, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Set.preimage_univ, Set.inter_univ, prodChartedSpace_chartAt]
  exact OpenPartialHomeomorph.prod_source _ _

/-- **The class coordinate of the inverse chart of the capping model.**  In the transparent
structure on `(0,∞) × ℝP³` the inverse of the preferred chart at `q` reads, in the class direction,
as the inverse of the preferred chart of `ℝP³` at `q.2`, followed by the inverse of the model change
`psiEquiv`. -/
theorem clsSurj_snd_chartAt_halfLine_symm (q : Set.Ioi (0:ℝ) × Projectivization ℝ (Work.Drive.Eucl 3))
    {u : EuclideanSpace ℝ (Fin 4)} (hu : u ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) q).target) :
    Prod.snd ((chartAt (EuclideanSpace ℝ (Fin 4)) q).symm u)
      = (chartAt (EuclideanSpace ℝ (Fin 3)) q.2).symm ((Work.Drive.psiEquiv.symm u).2) := by
  set x : Set.Ioi (0:ℝ) × Projectivization ℝ (Work.Drive.Eucl 3) :=
    (chartAt (EuclideanSpace ℝ (Fin 4)) q).symm u with hx
  have hxsrc : x ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) q).source :=
    OpenPartialHomeomorph.map_target _ hu
  have hright : chartAt (EuclideanSpace ℝ (Fin 4)) q x = u := by
    rw [hx]; exact OpenPartialHomeomorph.right_inv _ hu
  have hchart : chartAt (EuclideanSpace ℝ (Fin 4)) q x
      = Work.Drive.psiEquiv (chartAt (EuclideanSpace ℝ (Fin 1)) q.1 x.1,
          chartAt (EuclideanSpace ℝ (Fin 3)) q.2 x.2) := by
    have h : (fun x : Set.Ioi (0:ℝ) × Projectivization ℝ (Work.Drive.Eucl 3) =>
          @chartAt (EuclideanSpace ℝ (Fin 4)) _ _ _ Work.Drive.halfLineProjectiveCharted q x)
        = fun x => Work.Drive.psiEquiv (@chartAt
            (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3))) _ _ _
            (prodChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ))
              (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Work.Drive.Eucl 3))) q x) := rfl
    rw [congrFun h x, prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_apply]
  have h2 : Work.Drive.psiEquiv.symm u
      = (chartAt (EuclideanSpace ℝ (Fin 1)) q.1 x.1,
          chartAt (EuclideanSpace ℝ (Fin 3)) q.2 x.2) := by
    rw [← hright, hchart, Work.Drive.psiEquiv.symm_apply_apply]
  have h2' : (Work.Drive.psiEquiv.symm u).2 = chartAt (EuclideanSpace ℝ (Fin 3)) q.2 x.2 := by
    rw [h2]
  have hsrc : x.2 ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) q.2).source := by
    have h := clsSurj_source_chartAt_halfLine q
    rw [h] at hxsrc
    exact hxsrc.2
  rw [h2']
  exact (OpenPartialHomeomorph.left_inv _ hsrc).symm

/-- **The charted class map of the capping space, near a point, is the inverse model change.**  In
the chart of the transparent structure on the capping space at `p` and the projective chart at
`cls p`, the class map `cls` reads, near the base point, as the projection `u ↦ (psiEquiv.symm u).2`
of the model `ℝ⁴ = ℝ¹ × ℝ³` onto its class factor. -/
theorem clsSurj_eventually_chartAt_cls (p : Work.Drive.CappingSpace) :
    (fun u : EuclideanSpace ℝ (Fin 4) =>
        chartAt (EuclideanSpace ℝ (Fin 3)) (Work.Drive.cls p)
          (Work.Drive.cls ((chartAt (EuclideanSpace ℝ (Fin 4)) p).symm u)))
      =ᶠ[𝓝 ((chartAt (EuclideanSpace ℝ (Fin 4)) p) p)]
      (fun u => (Work.Drive.psiEquiv.symm u).2) := by
  set χ : OpenPartialHomeomorph Work.Drive.CappingSpace (EuclideanSpace ℝ (Fin 4)) :=
    chartAt (EuclideanSpace ℝ (Fin 4)) p with hχ
  set y₀ : EuclideanSpace ℝ (Fin 4) := χ p with hy₀
  set q : Set.Ioi (0:ℝ) × Projectivization ℝ (Work.Drive.Eucl 3) :=
    Work.Drive.cappingSpaceHomeoProj p with hq
  have hχsrc : p ∈ χ.source := by rw [hχ]; exact mem_chart_source _ _
  have hmem : y₀ ∈ χ.target := by rw [hy₀]; exact χ.map_source hχsrc
  have hcont : ContinuousAt (χ.symm : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace) y₀ :=
    χ.continuousAt_symm hmem
  have hleft : χ.symm y₀ = p := by
    rw [hy₀, hχ]; exact OpenPartialHomeomorph.left_inv _ hχsrc
  have hbase : Work.Drive.cappingSpaceHomeoProj (χ.symm y₀) = q := by rw [hleft, hq]
  have hmemq : Work.Drive.cappingSpaceHomeoProj (χ.symm y₀)
      ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) q).source := by
    rw [hbase]; exact mem_chart_source _ _
  -- Step 1: the pushed-forward chart of the capping space is the chart of the model along `e`.
  have hA : (fun u => (χ : Work.Drive.CappingSpace → EuclideanSpace ℝ (Fin 4)) (χ.symm u))
      =ᶠ[𝓝 y₀] fun u =>
        chartAt (EuclideanSpace ℝ (Fin 4)) q (Work.Drive.cappingSpaceHomeoProj (χ.symm u)) := by
    have h := eventuallyEq_chartAt_homeomorph_chartedSpace_self (H := EuclideanSpace ℝ (Fin 4))
      (Work.Drive.cappingSpaceHomeoProj.symm) (χ.symm) y₀ hcont
    rw [hleft] at h
    exact h
  -- Step 2: the two composites are both equal to `u` near the base point.
  have hB : (fun u => chartAt (EuclideanSpace ℝ (Fin 4)) q
        (Work.Drive.cappingSpaceHomeoProj (χ.symm u))) =ᶠ[𝓝 y₀] fun u => u := by
    have hC : (fun u => (χ : Work.Drive.CappingSpace → EuclideanSpace ℝ (Fin 4)) (χ.symm u))
        =ᶠ[𝓝 y₀] fun u => u := by
      filter_upwards [χ.open_target.mem_nhds hmem] with u hu
      exact OpenPartialHomeomorph.right_inv _ hu
    exact hA.symm.trans hC
  -- Step 3: hence the model coordinate of the capping point is the inverse chart of the model.
  have hcont2 : ContinuousAt (fun u => Work.Drive.cappingSpaceHomeoProj (χ.symm u)) y₀ :=
    Work.Drive.cappingSpaceHomeoProj.continuous.continuousAt.comp hcont
  have hmem2 : ∀ᶠ u in 𝓝 y₀, Work.Drive.cappingSpaceHomeoProj (χ.symm u)
      ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) q).source :=
    hcont2.preimage_mem_nhds
      ((chartAt (EuclideanSpace ℝ (Fin 4)) q).open_source.mem_nhds hmemq)
  have htargetE : ∀ᶠ u in 𝓝 y₀, u ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) q).target := by
    filter_upwards [hB, hmem2] with u hBu hu2
    have h := (chartAt (EuclideanSpace ℝ (Fin 4)) q).map_source hu2
    rwa [hBu] at h
  have hD : (fun u => Work.Drive.cappingSpaceHomeoProj (χ.symm u))
      =ᶠ[𝓝 y₀] fun u => (chartAt (EuclideanSpace ℝ (Fin 4)) q).symm u := by
    filter_upwards [hB, hmem2] with u hBu hu2
    have h1 : (chartAt (EuclideanSpace ℝ (Fin 4)) q).symm u
        = Work.Drive.cappingSpaceHomeoProj (χ.symm u) := by
      calc (chartAt (EuclideanSpace ℝ (Fin 4)) q).symm u
          = (chartAt (EuclideanSpace ℝ (Fin 4)) q).symm
              ((chartAt (EuclideanSpace ℝ (Fin 4)) q)
                (Work.Drive.cappingSpaceHomeoProj (χ.symm u))) := by rw [hBu]
        _ = Work.Drive.cappingSpaceHomeoProj (χ.symm u) :=
            OpenPartialHomeomorph.left_inv _ hu2
    exact h1.symm
  -- Step 4: the class of the capping point, in the model chart at `q`.
  have hE : (fun u => Work.Drive.cls (χ.symm u))
      =ᶠ[𝓝 y₀] fun u =>
        (chartAt (EuclideanSpace ℝ (Fin 3)) q.2).symm ((Work.Drive.psiEquiv.symm u).2) := by
    have hcls : (fun u => Work.Drive.cls (χ.symm u))
        = fun u => Prod.snd (Work.Drive.cappingSpaceHomeoProj (χ.symm u)) := by
      funext u; rw [Work.Drive.cls_apply]
    have h1 : (fun u => Prod.snd (Work.Drive.cappingSpaceHomeoProj (χ.symm u)))
        =ᶠ[𝓝 y₀] fun u => Prod.snd ((chartAt (EuclideanSpace ℝ (Fin 4)) q).symm u) := by
      filter_upwards [hD] with u hu
      rw [hu]
    have h2 : (fun u => Prod.snd ((chartAt (EuclideanSpace ℝ (Fin 4)) q).symm u))
        =ᶠ[𝓝 y₀] fun u =>
          (chartAt (EuclideanSpace ℝ (Fin 3)) q.2).symm ((Work.Drive.psiEquiv.symm u).2) := by
      filter_upwards [htargetE] with u hu
      exact clsSurj_snd_chartAt_halfLine_symm q hu
    rw [hcls]
    exact h1.trans h2
  -- Step 5: the projective chart at the class is the identity on its own inverse.
  have hstep : (fun u => chartAt (EuclideanSpace ℝ (Fin 3)) (Work.Drive.cls p)
        ((chartAt (EuclideanSpace ℝ (Fin 3)) q.2).symm ((Work.Drive.psiEquiv.symm u).2)))
      = fun u => (Work.Drive.psiEquiv.symm u).2 := by
    funext u
    have hq2 : q.2 = Work.Drive.cls p := by rw [hq]; rfl
    rw [hq2, projCharted_chartAt_eq_projChart (Work.Drive.cls p), projChart_symm_apply,
      projChart_apply, projChartMap_projChartInv]
  filter_upwards [hE] with u hu
  rw [hu, congrFun hstep u]

/-- The class projection of the capping space is continuous. -/
theorem clsSurj_continuousAt_cls (p : Work.Drive.CappingSpace) : ContinuousAt Work.Drive.cls p :=
  ((continuous_snd.comp Work.Drive.cappingSpaceHomeoProj.continuous).continuousAt).congr
    (Filter.Eventually.of_forall (fun q => by rw [Work.Drive.cls_apply]; rfl))

/-- **The class projection of the capping space is a submersion**: the manifold derivative of `cls`
(the projective class of a point of the capping space) is surjective at every point.  This is the one
missing brick of the *chart-free* pair producer `Drive/pairReg_of_loopBoxData`: it lets a spanning of
two derivatives in the `4`-dimensional capping tangent space be pushed forward to a spanning of the two
*class* derivatives in the `3`-dimensional class tangent space, through the chain rule and the
identities `cls (shadow lam hc p) = cls p` (`cls_shadow`) and `cls (clampedSweep c ψ P x) = cls (P (x 0, x 1))`.

Proof.  Write `e := cappingSpaceHomeoProj`, `q := e p`, so that `cls = Prod.snd ∘ e`.  In the chart of
the capping space at `p` (which is the chart of `(0,∞) × ℝP³` at `q` read along `e`) and the preferred
projective chart at `cls p = q.2`, the charted class map is, near the base point, the second
coordinate of `psiEquiv.symm` — the linear projection `ℝ⁴ = ℝ¹ × ℝ³ → ℝ³` (`clsSurj_eventually_chartAt_cls`).
Since that projection is onto, `HasMFDerivAt` gives the statement. -/
theorem mfderiv_cls_surjective (p : Work.Drive.CappingSpace) :
    Function.Surjective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (Work.Drive.cls) p) := by
  set L : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3))).comp
      (Work.Drive.psiEquiv.symm :
        EuclideanSpace ℝ (Fin 4) →L[ℝ] (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)))
    with hL
  have hLfun : (fun u : EuclideanSpace ℝ (Fin 4) => (Work.Drive.psiEquiv.symm u).2) = ⇑L := by
    funext u; rw [hL]; rfl
  have hfun : writtenInExtChartAt (𝓡 4) (𝓡 3) p Work.Drive.cls
      = fun u : EuclideanSpace ℝ (Fin 4) => chartAt (EuclideanSpace ℝ (Fin 3)) (Work.Drive.cls p)
          (Work.Drive.cls ((chartAt (EuclideanSpace ℝ (Fin 4)) p).symm u)) := by
    funext u
    simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp, id_eq]
  have hbase : (extChartAt (𝓡 4) p) p = (chartAt (EuclideanSpace ℝ (Fin 4)) p) p := by
    simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply, id_eq]
  have hderiv : HasFDerivWithinAt (writtenInExtChartAt (𝓡 4) (𝓡 3) p Work.Drive.cls) L
      (Set.range (𝓡 4)) ((extChartAt (𝓡 4) p) p) := by
    rw [hfun, hbase]
    refine ((Filter.EventuallyEq.hasFDerivAt_iff (clsSurj_eventually_chartAt_cls p)).mpr ?_).hasFDerivWithinAt
    rw [hLfun]
    exact L.hasFDerivAt
  have h : HasMFDerivAt (𝓡 4) (𝓡 3) Work.Drive.cls p L := ⟨clsSurj_continuousAt_cls p, hderiv⟩
  have hLsurj : Function.Surjective L := by
    intro w
    refine ⟨Work.Drive.psiEquiv (0, w), ?_⟩
    rw [hL]
    simp [Work.Drive.psiEquiv.symm_apply_apply]
  rw [h.mfderiv]
  exact hLsurj

end

end Work.Drive
