import Mathlib
import Submission.Work.Drive.refTripleProducerDefs
import Submission.Work.Drive.linCommonPoint
import Submission.Work.Drive.planeClassDeriv_eq_mfderiv
import Submission.Work.Drive.quotient_generalPosition
import Submission.Work.Drive.chartGenericity
import Submission.Work.Drive.exists_norm_lt_one_linPlaneChart_eq

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


namespace Work.Drive

/-!
# The general position `hV` of the three linear plane charts

`Work.Drive.endTripleReg_linPlaneCharts` (and, before it, the `hV` clause of
`Work.Drive.ClassTripleRegular`) asks, at a triple of parameters at which the three linear plane charts
`diskPlane (linPlaneChart (Φ k) c hc)` have a common class, for the triviality of the intersection of
the three class-derivative ranges:

> `range (mfderiv (planeClassMap (diskPlane (linPlaneChart (Φ k) c hc))) (y k))` for `k = 0,1,2`.

This file proves it.  The mathematical content is the fact that the tangent plane of the projective
plane `ℙ(linSub (Φ k))` at the common point is `linSub (Φ k) / L` (the quotient by the common line
`L`), so that the linear-algebra fact `Work.Drive.quotient_generalPosition` — three `3`-planes of `ℝ⁴`
with `1`-dimensional triple intersection have quotient tangent planes with trivial triple intersection —
applies.

## The route

* `Work.Drive.linPlaneLift φ` is the *lift* `y ↦ φ (linVecC (sqDisk (foldBox y)))` of the class map of
  `diskPlane (linPlaneChart φ c hc)`, so that the class map is `mk ∘ linPlaneLift`
  (`Work.Drive.planeClassMap_diskPlane_linPlaneChart_eq`); the lift takes all its values in the plane
  `linSub φ` (`Work.Drive.linPlaneLift_mem_linSub`).
* `Work.Drive.range_fderiv_le_of_mapsTo`: the derivative of a map into a (finite-dimensional, hence
  closed) submodule stays in that submodule — proved by the slope/limit argument.
* `Work.Drive.range_mfderiv_projMk_le_map`: consequently the range of the class derivative is contained
  in the image, under the projective quotient `projCoordFunDerivE i v` (whose kernel is `ℝ∙v`), of that
  submodule; this is `Work.Drive.range_mfderiv_projMk` plus the previous point.
* finally, the three base points are proportional
  (`Projectivization.mk_eq_mk_iff'` applied to the common class), so
  `Work.Drive.map_projCoordFunDerivE_smul` lets the three containments be expressed with the *same*
  projective quotient, and `Work.Drive.inf_map_eq_bot_iff` with the general position `hrank` closes the
  proof.

The hypotheses `hgen` (the boundary circle avoids the common point) is not needed: the containment
argument works at every parameter, and the common line is contained in each plane because the three
classes agree.
-/

open Manifold Set
open scoped Manifold ContDiff

attribute [local instance] Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-! ## 1. The lift of the class map of a folded linear plane chart -/

/-- The lift of the class map of the folded presentation `diskPlane (linPlaneChart φ c hc)`: the
projectivisation of this map is the class map. -/
def linPlaneLift (φ : Eucl 3 ≃L[ℝ] Eucl 3) (y : EuclideanSpace ℝ (Fin 2)) : Eucl 3 :=
  φ (linVecC (sqDisk (foldBox y)))

theorem linPlaneLift_contDiff (φ : Eucl 3 ≃L[ℝ] Eucl 3) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (linPlaneLift φ) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => linVecC (sqDisk (foldBox y))) :=
    linVecC_contDiff.comp (sqDisk_contDiff.comp (contMDiff_iff_contDiff.mp foldBox_contMDiff))
  exact φ.contDiff.comp h

lemma linPlaneLift_ne_zero (φ : Eucl 3 ≃L[ℝ] Eucl 3) (y : EuclideanSpace ℝ (Fin 2)) :
    linPlaneLift φ y ≠ 0 := phi_linVecC_ne_zero φ _

lemma linPlaneLift_mem_linSub (φ : Eucl 3 ≃L[ℝ] Eucl 3) (y : EuclideanSpace ℝ (Fin 2)) :
    linPlaneLift φ y ∈ linSub φ := linVecC_mem_linSub φ _

/-- **The class map of a folded linear plane chart is the projectivisation of its lift.** -/
lemma planeClassMap_diskPlane_linPlaneChart_eq (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) :
    planeClassMap (diskPlane (linPlaneChart φ c hc))
      = fun y => Projectivization.mk ℝ (linPlaneLift φ y) (linPlaneLift_ne_zero φ y) := by
  funext y
  simp only [planeClassMap, diskPlane, cappingSpaceHomeoProj_linPlaneChart, linPlaneLift]

/-! ## 2. The derivative of a map into a submodule stays in it -/

/-- **The derivative of a map with values in a submodule takes its values in that submodule.**  (The
submodule is finite-dimensional, hence closed, so it contains the limits of the difference quotients
`t⁻¹ • (g (y + t • w) - g y)` along the curve `t ↦ g (y + t • w)`, whose derivative is `dg(y) w`.) -/
theorem range_fderiv_le_of_mapsTo (V : EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (y : EuclideanSpace ℝ (Fin 2)) (hVd : DifferentiableAt ℝ V y)
    (S : Submodule ℝ (Eucl 3)) (hS : ∀ x, V x ∈ S) :
    LinearMap.range (fderiv ℝ V y).toLinearMap ≤ S := by
  rintro z ⟨w, rfl⟩
  have hcurve : HasDerivAt (fun t : ℝ => y + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
  have hderiv : HasDerivAt (fun t : ℝ => V (y + t • w)) ((fderiv ℝ V y) w) 0 := by
    have h0 : HasFDerivAt V (fderiv ℝ V y) (y + (0 : ℝ) • w) := by simpa using hVd.hasFDerivAt
    simpa [Function.comp_def] using h0.comp_hasDerivAt 0 hcurve
  have hclosed : IsClosed (S : Set (Eucl 3)) := Submodule.closed_of_finiteDimensional S
  refine hclosed.mem_of_tendsto hderiv.tendsto_slope ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact S.smul_mem _ (S.sub_mem (hS _) (hS _))

/-! ## 3. The containment of the class derivative in the projective tangent plane -/

/-- **The class derivative of a lift with values in a submodule is contained in the projective image of
that submodule.**  `Work.Drive.range_mfderiv_projMk` exhibits the range of the class derivative
`mfderiv (mk ∘ V) y` as the image, under the projective quotient `projCoordFunDerivE i (V y)` (whose
kernel is the line `ℝ∙(V y)`), of the range of `fderiv ℝ V y`; the range of the latter lies in `S` by
`Work.Drive.range_fderiv_le_of_mapsTo`, and images preserve containment. -/
theorem range_mfderiv_projMk_le_map (V : EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (hV : ∀ x, V x ≠ 0) (y : EuclideanSpace ℝ (Fin 2))
    (hVsm : ContMDiffAt (𝓡 2) (𝓘(ℝ, Eucl 3)) ((⊤ : ℕ∞) : WithTop ℕ∞) V y)
    (S : Submodule ℝ (Eucl 3)) (hS : ∀ x, V x ∈ S) :
    (mfderiv (𝓡 2) (𝓡 3) (fun x => Projectivization.mk ℝ (V x) (hV x)) y).range
      ≤ Submodule.map (projCoordFunDerivE
          (projChartIndexOf (Projectivization.mk ℝ (V y) (hV y))) (V y)).toLinearMap S := by
  rw [range_mfderiv_projMk V hV y hVsm]
  refine Submodule.map_mono ?_
  exact range_fderiv_le_of_mapsTo V y (hVsm.contDiffAt.differentiableAt (by simp)) S hS

/-! ## 4. The target -/

theorem linPlaneTripleRange
    (Φ : Fin 3 → Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (c : ℝ) (hc : 0 < c)
    (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, Work.Drive.linSub (Φ k)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      Work.Drive.linPlaneChart (Φ k) c hc z ≠ Work.Drive.linCommonPt Φ c hc hrank)
    (y : Fin 3 → EuclideanSpace ℝ (Fin 2))
    (hcom : ∀ k : Fin 3,
      Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 2) c hc)) (y 2) =
        Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ k) c hc)) (y k)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Work.Drive.Eucl 3)) :=
      Work.Drive.projCharted 3
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (Work.Drive.Ctop)
      (Projectivization ℝ (Work.Drive.Eucl 3)) := Work.Drive.isManifold_projCharted 3
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 0) c hc)))
      (y 0)).range ⊓
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 1) c hc)))
      (y 1)).range ⊓
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 2) c hc)))
      (y 2)).range = ⊥ := by
  set V : Fin 3 → EuclideanSpace ℝ (Fin 2) → Eucl 3 := fun k => linPlaneLift (Φ k) with hVdef
  have hVne : ∀ k x, V k x ≠ 0 := fun k x => linPlaneLift_ne_zero (Φ k) x
  have hVsm : ∀ k x, ContMDiffAt (𝓡 2) (𝓘(ℝ, Eucl 3)) ((⊤ : ℕ∞) : WithTop ℕ∞) (V k) x :=
    fun k x => (contMDiff_iff_contDiff.mpr (linPlaneLift_contDiff (Φ k))).contMDiffAt
  have hVmem : ∀ k x, V k x ∈ linSub (Φ k) := fun k x => linPlaneLift_mem_linSub (Φ k) x
  have hcls : ∀ k, planeClassMap (diskPlane (linPlaneChart (Φ k) c hc))
      = fun x => Projectivization.mk ℝ (V k x) (hVne k x) := by
    intro k
    rw [planeClassMap_diskPlane_linPlaneChart_eq (Φ k) c hc]
  rw [hcls 0, hcls 1, hcls 2]
  -- the three lifts at the three parameters are proportional: the classes agree
  have hco : ∀ k, ∃ t : ℝ, t ≠ 0 ∧ V k (y k) = t • V 0 (y 0) := by
    intro k
    have h2 : Projectivization.mk ℝ (V 2 (y 2)) (hVne 2 (y 2))
        = Projectivization.mk ℝ (V k (y k)) (hVne k (y k)) := by
      have h := hcom k
      rw [hcls 2, hcls k] at h
      exact h
    have h0 : Projectivization.mk ℝ (V 0 (y 0)) (hVne 0 (y 0))
        = Projectivization.mk ℝ (V 2 (y 2)) (hVne 2 (y 2)) := by
      have h := hcom 0
      rw [hcls 2, hcls 0] at h
      exact h.symm
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ (V 2 (y 2)) (V k (y k))
      (hVne 2 (y 2)) (hVne k (y k))).mp h2
    obtain ⟨b, hb⟩ := (Projectivization.mk_eq_mk_iff' ℝ (V 0 (y 0)) (V 2 (y 2))
      (hVne 0 (y 0)) (hVne 2 (y 2))).mp h0
    have ha0 : a ≠ 0 := fun h => hVne 2 (y 2) (by rw [h, zero_smul] at ha; exact ha.symm)
    have hb0 : b ≠ 0 := fun h => hVne 0 (y 0) (by rw [h, zero_smul] at hb; exact hb.symm)
    refine ⟨a⁻¹ * b⁻¹, mul_ne_zero (inv_ne_zero ha0) (inv_ne_zero hb0), ?_⟩
    have ha' : V k (y k) = a⁻¹ • V 2 (y 2) := by
      have h := congrArg (fun z => a⁻¹ • z) ha
      rwa [inv_smul_smul₀ ha0] at h
    have hb' : V 2 (y 2) = b⁻¹ • V 0 (y 0) := by
      have h := congrArg (fun z => b⁻¹ • z) hb
      rwa [inv_smul_smul₀ hb0] at h
    rw [ha', hb', smul_smul]
  -- each range lies in the image of the plane `linSub (Φ k)` under one and the same quotient
  have hle : ∀ k : Fin 3,
      (mfderiv (𝓡 2) (𝓡 3) (fun x => Projectivization.mk ℝ (V k x) (hVne k x)) (y k)).range
        ≤ Submodule.map (projCoordFunDerivE
            (projChartIndexOf (Projectivization.mk ℝ (V 0 (y 0)) (hVne 0 (y 0)))) (V 0 (y 0))).toLinearMap
          (linSub (Φ k)) := by
    intro k
    obtain ⟨t, ht, hVk⟩ := hco k
    have hraw := range_mfderiv_projMk_le_map (V k) (hVne k) (y k) (hVsm k (y k))
      (linSub (Φ k)) (hVmem k)
    have hpt : Projectivization.mk ℝ (V k (y k)) (hVne k (y k))
        = Projectivization.mk ℝ (V 0 (y 0)) (hVne 0 (y 0)) :=
      (Projectivization.mk_eq_mk_iff' ℝ (V k (y k)) (V 0 (y 0))
        (hVne k (y k)) (hVne 0 (y 0))).mpr ⟨t, hVk.symm⟩
    have hi : projChartIndexOf (Projectivization.mk ℝ (V k (y k)) (hVne k (y k)))
        = projChartIndexOf (Projectivization.mk ℝ (V 0 (y 0)) (hVne 0 (y 0))) :=
      congrArg projChartIndexOf hpt
    have hmap : Submodule.map (projCoordFunDerivE
          (projChartIndexOf (Projectivization.mk ℝ (V k (y k)) (hVne k (y k)))) (V k (y k))).toLinearMap
          (linSub (Φ k))
        = Submodule.map (projCoordFunDerivE
          (projChartIndexOf (Projectivization.mk ℝ (V 0 (y 0)) (hVne 0 (y 0)))) (V 0 (y 0))).toLinearMap
          (linSub (Φ k)) := by
      rw [hi, hVk, map_projCoordFunDerivE_smul _ _ ht]
    exact hraw.trans_eq hmap
  -- the common lift lies in all three planes; the planes meet in exactly its line by `hrank`
  have hmem : ∀ k : Fin 3, V 0 (y 0) ∈ linSub (Φ k) := by
    intro k
    obtain ⟨t, ht, hVk⟩ := hco k
    have ht' : V 0 (y 0) = t⁻¹ • V k (y k) := by
      have h := congrArg (fun z => t⁻¹ • z) hVk.symm
      rwa [inv_smul_smul₀ ht] at h
    rw [ht']
    exact Submodule.smul_mem _ _ (hVmem k (y k))
  have hInf : (⨅ k : Fin 3, linSub (Φ k)) = linSub (Φ 0) ⊓ linSub (Φ 1) ⊓ linSub (Φ 2) := by
    refine le_antisymm ?_ ?_
    · exact le_inf (le_inf (iInf_le _ 0) (iInf_le _ 1)) (iInf_le _ 2)
    · refine le_iInf fun k => ?_
      fin_cases k
      · exact inf_le_left.trans inf_le_left
      · exact inf_le_left.trans inf_le_right
      · exact inf_le_right
  have hinter : linSub (Φ 0) ⊓ linSub (Φ 1) ⊓ linSub (Φ 2)
      = Submodule.span ℝ ({V 0 (y 0)} : Set (Eucl 3)) := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨⟨hmem 0, hmem 1⟩, hmem 2⟩
    · rw [finrank_span_singleton (hVne 0 (y 0)), ← hInf, hrank]
  -- the quotient at the common line kills the triple intersection of the three planes
  have hker : LinearMap.ker (projCoordFunDerivE
      (projChartIndexOf (Projectivization.mk ℝ (V 0 (y 0)) (hVne 0 (y 0)))) (V 0 (y 0))).toLinearMap
      = Submodule.span ℝ ({V 0 (y 0)} : Set (Eucl 3)) := by
    have hvi : (V 0 (y 0)).ofLp
        (projChartIndexOf (Projectivization.mk ℝ (V 0 (y 0)) (hVne 0 (y 0)))) ≠ 0 :=
      (mem_projChartSource_iff' (hVne 0 (y 0))).mp (projChartIndexOf_spec _)
    ext w
    rw [LinearMap.mem_ker]
    exact projCoordFunDerivE_eq_zero_iff hvi w
  have hW : ∀ k : Fin 3, Submodule.span ℝ ({V 0 (y 0)} : Set (Eucl 3)) ≤ linSub (Φ k) := by
    intro k
    rw [Submodule.span_singleton_le_iff_mem]
    exact hmem k
  have hbot := (inf_map_eq_bot_iff (projCoordFunDerivE
      (projChartIndexOf (Projectivization.mk ℝ (V 0 (y 0)) (hVne 0 (y 0)))) (V 0 (y 0)))
      hker (fun k => linSub (Φ k)) hW).mpr hinter
  -- assemble
  have hle0 : ((mfderiv (𝓡 2) (𝓡 3) (fun x => Projectivization.mk ℝ (V 0 x) (hVne 0 x)) (y 0)).range
        ⊓ (mfderiv (𝓡 2) (𝓡 3) (fun x => Projectivization.mk ℝ (V 1 x) (hVne 1 x)) (y 1)).range
        ⊓ (mfderiv (𝓡 2) (𝓡 3) (fun x => Projectivization.mk ℝ (V 2 x) (hVne 2 x)) (y 2)).range)
      ≤ Submodule.map (projCoordFunDerivE
          (projChartIndexOf (Projectivization.mk ℝ (V 0 (y 0)) (hVne 0 (y 0)))) (V 0 (y 0))).toLinearMap
          (linSub (Φ 0)) :=
    (inf_le_left.trans inf_le_left).trans (hle 0)
  have hle1 : ((mfderiv (𝓡 2) (𝓡 3) (fun x => Projectivization.mk ℝ (V 0 x) (hVne 0 x)) (y 0)).range
        ⊓ (mfderiv (𝓡 2) (𝓡 3) (fun x => Projectivization.mk ℝ (V 1 x) (hVne 1 x)) (y 1)).range
        ⊓ (mfderiv (𝓡 2) (𝓡 3) (fun x => Projectivization.mk ℝ (V 2 x) (hVne 2 x)) (y 2)).range)
      ≤ Submodule.map (projCoordFunDerivE
          (projChartIndexOf (Projectivization.mk ℝ (V 0 (y 0)) (hVne 0 (y 0)))) (V 0 (y 0))).toLinearMap
          (linSub (Φ 1)) :=
    (inf_le_left.trans inf_le_right).trans (hle 1)
  have hle2 : ((mfderiv (𝓡 2) (𝓡 3) (fun x => Projectivization.mk ℝ (V 0 x) (hVne 0 x)) (y 0)).range
        ⊓ (mfderiv (𝓡 2) (𝓡 3) (fun x => Projectivization.mk ℝ (V 1 x) (hVne 1 x)) (y 1)).range
        ⊓ (mfderiv (𝓡 2) (𝓡 3) (fun x => Projectivization.mk ℝ (V 2 x) (hVne 2 x)) (y 2)).range)
      ≤ Submodule.map (projCoordFunDerivE
          (projChartIndexOf (Projectivization.mk ℝ (V 0 (y 0)) (hVne 0 (y 0)))) (V 0 (y 0))).toLinearMap
          (linSub (Φ 2)) :=
    inf_le_right.trans (hle 2)
  exact le_bot_iff.mp (le_trans (le_inf (le_inf hle0 hle1) hle2) (le_of_eq hbot))

end

end Work.Drive
