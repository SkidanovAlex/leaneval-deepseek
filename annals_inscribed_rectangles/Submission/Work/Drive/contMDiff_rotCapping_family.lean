import Mathlib
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.rotLens_rotCapping_isAction
import Submission.Work.Drive.cappingSpaceHomeoProj_rotCapping
import Submission.Work.Drive.projRotSmooth
import Submission.Work.Drive.contMDiffAt_projMk
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff_general
import Submission.Work.Drive.chartedStructure_contMDiffWithinAt
import Submission.Work.Drive.contMDiffAt_projChartMap
import Submission.Work.Drive.contMDiffAt_projCharted_iff

/-!
# The rotation of the capping space is smooth in the rotation parameter

This file proves `Work.Drive.contMDiff_rotCapping_family`: for a `C^∞` family
`P : ℝ² → CappingSpace` of points of the capping space, the *rotated* family

`(p₁, p₂) ↦ rotCapping (p₁ 0) (P p₂)`

is `C^∞` as a map `ℝ¹ × ℝ² → CappingSpace`.  This is the smoothness input of the rotation action
on the capping space, i.e. of the fact that the rotation of the paper's planes varies smoothly with
the angle.

The proof strategy is the one recorded in `Submission/Work/Drive/ROT_SMOOTHNESS_STATUS.md`:

* the rotation of the capping space fixes the radial coordinate of
  `cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³` and acts on the `ℝP³`-factor by
  `Work.Drive.projRot` (`cappingSpaceHomeoProj_rotCapping`), so smoothness of a map into
  `CappingSpace` reduces (by transport of the charted structure, `chartedStructure_contMDiffWithinAt`)
  to smoothness of the composite into `(0,∞) × ℝP³`, which splits into its two components
  (`contMDiffAt_halfLineProjective_iff_general`);
* the first component does not move at all;
* the second is handled by choosing a projective chart `i` at the value of the un-rotated
  `ℝP³`-coordinate, rewriting `projRot t ∘ projChartInv i = [diagRot t ∘ projSection i]` there, and
  applying `contMDiffAt_projMk` to the explicit lift `diagRot (t ·) (projSection i (·))`.

The main theorem is then obtained by flattening the product source `ℝ¹ × ℝ²` to `ℝ³` along
`EuclideanSpace.finAddEquivProd`.
-/

namespace Work.Drive

attribute [local instance] Work.Drive.cappingCharted

open scoped Manifold ContDiff

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

open Manifold Topology Filter LinearAlgebra.Projectivization

/-- **`cappingSpaceHomeoProj` is `C^∞`** for the transparent smooth structures on the capping space
and on its model `(0,∞) × ℝP³`. -/
theorem contMDiffAt_cappingSpaceHomeoProj (p₀ : CappingSpace) :
    @ContMDiffAt ℝ _ (EuclideanSpace ℝ (Fin 4)) _ _ (EuclideanSpace ℝ (Fin 4)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      CappingSpace _ cappingCharted
      (EuclideanSpace ℝ (Fin 4)) _ _ (EuclideanSpace ℝ (Fin 4)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _ halfLineProjectiveCharted
      ((⊤ : ℕ∞) : WithTop ℕ∞) cappingSpaceHomeoProj p₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := halfLineProjectiveCharted
  have h := (chartedStructure_contMDiffWithinAt
    (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (M' := CappingSpace) (e := cappingSpaceHomeoProj.symm)
    (Z := CappingSpace) (f := id) Set.univ p₀).mp
    (contMDiffWithinAt_id (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  simpa only [cappingCharted, contMDiffWithinAt_univ, Function.comp_def, id_eq,
    Homeomorph.symm_symm] using h

/-- **The `S¹`-rotation action of the capping space is smooth in the rotation parameter**, in the
flattened form: for `C^∞` maps `t : ℝᵏ → ℝ` and `P : ℝᵏ → CappingSpace`, the family
`u ↦ rotCapping (t u) (P u)` is `C^∞`. -/
theorem contMDiffAt_rotCapping_family {k : ℕ}
    (t : EuclideanSpace ℝ (Fin k) → ℝ) (P : EuclideanSpace ℝ (Fin k) → CappingSpace)
    (ht : ContMDiff (𝓡 k) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) t)
    (hP : ContMDiff (𝓡 k) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (u₀ : EuclideanSpace ℝ (Fin k)) :
    ContMDiffAt (𝓡 k) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => rotCapping ((t u : ℝ) : UnitAddCircle) (P u)) u₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := halfLineProjectiveCharted
  set H : EuclideanSpace ℝ (Fin k) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun u => (cappingSpaceHomeoProj (P u)).2 with hH
  -- smoothness of the un-rotated projection into the model `(0,∞) × ℝP³`
  have hG₀ : ContMDiffAt (𝓡 k) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => cappingSpaceHomeoProj (P u)) u₀ :=
    (contMDiffAt_cappingSpaceHomeoProj (P u₀)).comp u₀ (hP u₀)
  have hsplit := (contMDiffAt_halfLineProjective_iff_general (𝓡 k)
      (fun u => cappingSpaceHomeoProj (P u)) u₀).mp hG₀
  have hrad₀ : ContMDiffAt (𝓡 k) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => expHomeo.symm ((cappingSpaceHomeoProj (P u)).1)) u₀ := hsplit.1
  have hHsm : ContMDiffAt (𝓡 k) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) H u₀ := by
    rw [hH]; exact hsplit.2
  -- a projective chart at the value of `H`
  obtain ⟨i, hi⟩ := exists_mem_projChartSource (H u₀)
  have hHcont : ContinuousAt H u₀ := hHsm.continuousAt
  have hchart : ContMDiffAt (𝓡 k) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => projChartMap i (H u)) u₀ :=
    ((contMDiffAt_projCharted_iff (f := H) u₀ i hi).mp hHsm).2
  have hφC : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => projChartMap i (H u)) u₀ :=
    hchart.contDiffAt
  -- smoothness of the lift `u ↦ diagRot (t u) (projSection i (projChartMap i (H u)))`
  have htC : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) t u₀ :=
    contMDiffAt_iff_contDiffAt.mp (ht u₀)
  have hsmooth : ContMDiffAt (𝓡 k) 𝓘(ℝ, Eucl 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => diagRot (t u) (projSection (n := 3) i (projChartMap i (H u)))) u₀ := by
    rw [contMDiffAt_iff_contDiffAt]
    have hc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => circ (t u)) u₀ :=
      contDiff_circ.contDiffAt.comp u₀ htC
    have hs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => star (circ (t u))) u₀ := by
      have h : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => circ (-(t u))) u₀ :=
        contDiff_circ.contDiffAt.comp u₀ htC.neg
      rwa [show (fun u => circ (-(t u))) = fun u => star (circ (t u)) from
        funext (fun u => circ_neg (t u))] at h
    have hsec : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u => projSection (n := 3) i (projChartMap i (H u))) u₀ :=
      (contDiff_projSection 3 i).contDiffAt.comp u₀ hφC
    have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u => c₁ (projSection (n := 3) i (projChartMap i (H u)))) u₀ := by
      have h := (confProjVecOf_c₁CLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt.comp
        u₀ hsec
      simpa only [Function.comp_def, confProjVecOf_c₁CLM_apply] using h
    have hB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u => c₂ (projSection (n := 3) i (projChartMap i (H u)))) u₀ := by
      have h := (confProjVecOf_c₂CLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt.comp
        u₀ hsec
      simpa only [Function.comp_def, confProjVecOf_c₂CLM_apply] using h
    exact confProjVecOf_contDiffAt_ofComplex (hc.mul hA) (hs.mul hB)
  -- smoothness of the rotated projective point, by the projective lift criterion
  have hVproj : ContMDiffAt (𝓡 k) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => Projectivization.mk ℝ
        (diagRot (t u) (projSection (n := 3) i (projChartMap i (H u))))
        (diagRot_ne_zero (t u) (projSection_ne_zero i (projChartMap i (H u))))) u₀ :=
    contMDiffAt_projMk (n := 3) (k := k)
      (fun u => diagRot (t u) (projSection (n := 3) i (projChartMap i (H u))))
      (fun u => diagRot_ne_zero (t u) (projSection_ne_zero i (projChartMap i (H u))))
      u₀ hsmooth
  have hev : ∀ᶠ u in 𝓝 u₀, H u ∈ projChartSource i :=
    hHcont.preimage_mem_nhds ((isOpen_projChartSource i).mem_nhds hi)
  have hproj : ContMDiffAt (𝓡 k) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => projRot (t u) (H u)) u₀ := by
    refine hVproj.congr_of_eventuallyEq ?_
    filter_upwards [hev] with u hu
    conv_lhs => rw [← projChartInv_projChartMap hu]
    rw [show projChartInv i (projChartMap i (H u))
        = Projectivization.mk ℝ (projSection (n := 3) i (projChartMap i (H u)))
            (projSection_ne_zero i (projChartMap i (H u))) from rfl,
      projRot_mk]
  -- assemble the two components of the rotated family in the model
  set G : EuclideanSpace ℝ (Fin k) →
      Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun u => cappingSpaceHomeoProj (rotCapping ((t u : ℝ) : UnitAddCircle) (P u)) with hG
  have hGsm : ContMDiffAt (𝓡 k) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) G u₀ := by
    refine (contMDiffAt_halfLineProjective_iff_general (𝓡 k) G u₀).mpr ⟨?_, ?_⟩
    · have hfun : (fun u => expHomeo.symm (G u).1)
          = fun u => expHomeo.symm ((cappingSpaceHomeoProj (P u)).1) := by
        funext u
        simp only [hG, cappingSpaceHomeoProj_rotCapping]
      rw [hfun]
      exact hrad₀
    · have hfun : (fun u => (G u).2)
          = fun u => projRot (t u) ((cappingSpaceHomeoProj (P u)).2) := by
        funext u
        simp only [hG, cappingSpaceHomeoProj_rotCapping]
      rw [hfun]
      simpa only [H] using hproj
  -- transport back to the capping space
  refine (chartedStructure_contMDiffWithinAt
    (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (I' := 𝓡 k)
    (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (M' := CappingSpace) (e := cappingSpaceHomeoProj.symm)
    (Z := EuclideanSpace ℝ (Fin k))
    (f := fun u => rotCapping ((t u : ℝ) : UnitAddCircle) (P u)) Set.univ u₀).mpr ?_
  simpa only [cappingCharted, contMDiffWithinAt_univ, hG, Homeomorph.symm_symm] using hGsm

theorem contMDiff_rotCapping_family (P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P) :
    ContMDiff (ModelWithCorners.prod (𝓡 1) (𝓡 2)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.rotCapping ((p.1 0 : ℝ) : UnitAddCircle) (P p.2)) := by
  let ι : EuclideanSpace ℝ (Fin 3) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) :=
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 2)
  let tCLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    (PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0).comp
      ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 2))).comp
        ι.toContinuousLinearMap)
  let aCLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 2))).comp
      ι.toContinuousLinearMap
  set Ft : EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    fun u => rotCapping (((ι u).1 0 : ℝ) : UnitAddCircle) (P (ι u).2) with hFt
  have ht : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) tCLM := tCLM.contMDiff
  have hQ : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => P (aCLM u)) :=
    hP.comp aCLM.contMDiff
  have hFt_sm : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Ft := by
    intro u
    rw [hFt]
    exact contMDiffAt_rotCapping_family (fun u : EuclideanSpace ℝ (Fin 3) => (ι u).1 0)
      (fun u : EuclideanSpace ℝ (Fin 3) => P (ι u).2) ht hQ u
  have hsym : ContMDiff (ModelWithCorners.prod (𝓡 1) (𝓡 2)) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑ι.symm) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact ι.symm.toContinuousLinearMap.contMDiff
  have hcomp := hFt_sm.comp hsym
  refine hcomp.congr ?_
  intro p
  rw [hFt, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]

end

end Work.Drive
