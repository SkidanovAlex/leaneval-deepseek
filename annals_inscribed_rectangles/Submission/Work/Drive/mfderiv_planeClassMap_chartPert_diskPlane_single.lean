import Mathlib
import Submission.Work.Drive.classTripleRegular
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.mfderiv_planeClassMap_diskPlane_single
import Submission.Work.Drive.chartPertData
import Submission.Work.Drive.encodedFamily
import Submission.Work.Drive.exists_chartPert
import Submission.Work.Drive.chartGenericity
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.cappingCharted

/-!
# The fold degeneracy of the class map of a *perturbed* disk presentation

`Work.Drive.mfderiv_planeClassMap_diskPlane_single` proves that the class map of the folded disk
presentation `diskPlane Q = Q ∘ sqDisk ∘ foldBox` has vanishing directional derivative in the fold
directions `eᵢ` at every `y` with `y i ∈ {0,1}`: the fold `foldBox` is reflection symmetric about such
a `y` in the direction `eᵢ`, so its derivative kills that direction and the class map cannot see it.

This file is the same statement for the **perturbed** presentation `z ↦ chartPert τ (diskPlane Q z)`
used by the genericity design.  The chart perturbation acts on the capping model as
`(level, class) ↦ (levelScale, classMap τ)` (`Work.Drive.cappingSpaceHomeoProj_chartPert`,
`Work.Drive.coordFam`), so it only multiplies the second coordinate of the *class map*:

`planeClassMap (fun z => chartPert τ (diskPlane Q z)) = classMap τ ∘ planeClassMap (diskPlane Q)`.

The degeneration therefore survives the perturbation: the chain rule factors the derivative of the
perturbed class map through the same degenerate inner factor
`mfderiv (fun z => sqDisk (foldBox z)) y eᵢ = 0` of the unperturbed one
(`Work.Drive.mfd_foldBox_add_single_eq_sub`, `Work.Drive.fderiv_apply_eq_zero_of_reflect_symm`,
`Work.Drive.mfderiv_cls_diskPlane`).

The one new ingredient is the smoothness of the class action `classMap τ` in the *point*
(`contMDiffAt_classMap_point`, the pointwise form of `Work.Drive.contMDiffAt_classMap_prod`), which
supplies the differentiability of the outer factor of the chain rule.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The class action `classMap τ` is `C^∞` in the point.**  This is the pointwise form of
`Work.Drive.contMDiffAt_classMap_prod` at a fixed parameter `τ`, in the shape needed as the outer
differentiability hypothesis of the chain rule for `planeClassMap (chartPert τ ∘ diskPlane Q)`. -/
theorem contMDiffAt_classMap_point (τ : Work.Drive.Eucl 3)
    (p : Projectivization ℝ (Work.Drive.Eucl 3)) :
    ContMDiffAt (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.classMap τ) p := by
  set F₂ : Eucl 3 × Projectivization ℝ (Eucl 3) → Projectivization ℝ (Eucl 3) :=
    fun u => classMap u.1 u.2 with hF₂
  have h1 : ContMDiffAt (𝓡 3) ((𝓡 4).prod (𝓡 3)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : Projectivization ℝ (Eucl 3) => (τ, s)) p :=
    ContMDiffAt.prodMk (contMDiffAt_const (c := τ)) contMDiffAt_id
  have h2 : ContMDiffAt ((𝓡 4).prod (𝓡 3)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) F₂ (τ, p) := by
    have h := contMDiffAt_classMap_prod τ p
    simpa only [hF₂] using h
  have hcomp := h2.comp p h1
  simpa only [F₂, Function.comp_def] using hcomp

set_option backward.isDefEq.respectTransparency false

theorem mfderiv_planeClassMap_chartPert_diskPlane_single (Q : ℂ → Work.Drive.CappingSpace)
    (τ : Work.Drive.Eucl 3) (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2)
    (hy : y i = 0 ∨ y i = 1) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) Work.Drive.CappingSpace :=
      Work.Drive.cappingCharted
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) Work.Drive.CappingSpace :=
      Work.Drive.isManifold_cappingCharted
    letI : T2Space Work.Drive.CappingSpace := Work.Drive.t2Space_cappingSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Work.Drive.Eucl 3)) :=
      Work.Drive.projCharted 3
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Work.Drive.Eucl 3)) :=
      Work.Drive.isManifold_projCharted 3
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) Q →
    mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (Work.Drive.planeClassMap
        (fun z => Work.Drive.chartPert τ (Work.Drive.diskPlane Q z))) y
      (EuclideanSpace.single i (1 : ℝ)) = 0 := by
  intro hQ
  -- the perturbation only changes the class coordinate of the presentation
  have hfac : planeClassMap (fun z => chartPert τ (diskPlane Q z))
      = classMap τ ∘ planeClassMap (diskPlane Q) := by
    funext z
    simp only [Function.comp_apply, planeClassMap, cappingSpaceHomeoProj_chartPert, coordFam_snd]
  rw [hfac]
  -- the outer factor of the chain rule is differentiable
  have hcls : MDifferentiableAt (𝓡 3) (𝓡 3) (classMap τ) (planeClassMap (diskPlane Q) y) :=
    (contMDiffAt_classMap_point τ _).mdifferentiableAt (by simp)
  -- the inner (folded) factor of the chain rule is differentiable
  have hf : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (cappingSpaceHomeoProj (Q z)).2) (sqDisk (foldBox y)) :=
    mdifferentiableAt_cls_of_contMDiff_cplx hQ _
  have hfold : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) foldBox :=
    contDiff_iff_contDiffAt.mpr fun y => contMDiffAt_iff_contDiffAt.mp (foldBox_contMDiff y)
  have hsqC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox z)) :=
    sqDisk_contDiff.comp hfold
  have hsq : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℂ))
      (fun z : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox z)) y :=
    (contMDiffAt_iff_contDiffAt.mpr (hsqC.contDiffAt)).mdifferentiableAt (by simp)
  have hfmd : MDifferentiableAt (𝓡 2) (𝓡 3) (planeClassMap (diskPlane Q)) y := by
    have hfun : (fun z : EuclideanSpace ℝ (Fin 2) =>
          (cappingSpaceHomeoProj (Q (sqDisk (foldBox z)))).2) = planeClassMap (diskPlane Q) := by
      funext z
      simp only [planeClassMap, diskPlane_apply]
    rw [← hfun]
    have h := hf.comp y hsq
    simpa only [Function.comp_def] using h
  have hchain := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓡 3)
    (f := planeClassMap (diskPlane Q)) (g := classMap τ) y hcls hfmd
  -- the fold kills the direction `eᵢ` for the square-to-disk parametrisation
  have hfold_diff : DifferentiableAt ℝ foldBox y :=
    (contMDiffAt_iff_contDiffAt.mp (foldBox_contMDiff y)).differentiableAt (by simp)
  have hbox : fderiv ℝ foldBox y (EuclideanSpace.single i (1 : ℝ)) = 0 :=
    fderiv_apply_eq_zero_of_reflect_symm foldBox y (EuclideanSpace.single i (1 : ℝ)) hfold_diff
      (mfd_foldBox_add_single_eq_sub y i hy)
  have hsqdiff : DifferentiableAt ℝ sqDisk (foldBox y) :=
    sqDisk_contDiff.contDiffAt.differentiableAt (by simp)
  have hgd : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox z)) y
      (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    change fderiv ℝ (sqDisk ∘ foldBox) y (EuclideanSpace.single i (1 : ℝ)) = 0
    rw [fderiv_comp y hsqdiff hfold_diff, ContinuousLinearMap.comp_apply, hbox, map_zero]
  have hinner : mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
      (fun z : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox z)) y
      (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    rw [mfderiv_eq_fderiv]
    exact hgd
  -- hence the class map of the *unperturbed* folded presentation has vanishing derivative there
  have hm : mfderiv (𝓡 2) (𝓡 3) (planeClassMap (diskPlane Q)) y
      (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    have hmain := mfderiv_cls_diskPlane Q y hf
    simp only [diskPlane_apply] at hmain
    change mfderiv (𝓡 2) (𝓡 3)
      (fun z : EuclideanSpace ℝ (Fin 2) => (cappingSpaceHomeoProj (Q (sqDisk (foldBox z)))).2) y
      (EuclideanSpace.single i (1 : ℝ)) = 0
    rw [hmain, ContinuousLinearMap.comp_apply, hinner, map_zero]
  -- and so does the perturbed one, by the chain rule
  have hfin : ((mfderiv (𝓡 3) (𝓡 3) (classMap τ) (planeClassMap (diskPlane Q) y)).comp
      (mfderiv (𝓡 2) (𝓡 3) (planeClassMap (diskPlane Q)) y))
      ((EuclideanSpace.single i (1 : ℝ) : TangentSpace (𝓡 2) y)) = 0 := by
    rw [ContinuousLinearMap.comp_apply, hm, map_zero]
  rw [hchain]
  exact hfin

end

end Work.Drive
