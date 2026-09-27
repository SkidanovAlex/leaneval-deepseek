import Mathlib
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.planeClassDeriv_eq_mfderiv
import Submission.Work.Drive.injective_fderiv_sqDisk_foldBox

/-!
# The class derivative of the folded plane presentation

The two plane conditions `hc` (immersion) and `hV` (general position) of the assembled parity identity
(`Work.Drive.even_sum_topBdryMeet_add_bottomBdryMeet_clamped_of_planeImmersion`) are statements about
`mfderiv (𝓡 2) (𝓡 3) (cls ∘ P k)`, where `cls` is the projective class of a capping point.  For the
**folded** presentation of the plane, `Work.Drive.diskPlane Q = Q ∘ sqDisk ∘ foldBox`
(`Submission/Work/Drive/planeChain.lean`), the chain rule factors this derivative:

> `mfderiv (cls ∘ diskPlane Q) y
>    = (mfderiv (cls ∘ Q) (sqDisk (foldBox y))) ∘ (mfderiv (sqDisk ∘ foldBox) y)`

(`Work.Drive.mfderiv_cls_diskPlane`), so the immersion hypothesis splits into

* the disk presentation `Q` is an immersion (`mfderiv (cls ∘ Q)` injective), and
* the square-to-disk parametrisation `sqDisk ∘ foldBox` is an immersion on the open square
  (its fold `foldFun x = (1 - cos (π x))/2` has derivative `π sin (π x)/2`, which vanishes exactly at
  the integers, and the Jacobian of `sqDisk` is non-singular off the corners).

The second factor is the one that *fails* on the seam, which is why the intrinsic form of the parity
identity only asks for `hc`/`hV` on the open square.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

set_option backward.isDefEq.respectTransparency false

noncomputable section

set_option maxHeartbeats 4000000

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- **The chain rule for the class map of the folded plane presentation.** -/
theorem mfderiv_cls_diskPlane (Q : ℂ → Work.Drive.CappingSpace) (y : EuclideanSpace ℝ (Fin 2))
    (hf : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
      (Work.Drive.sqDisk (Work.Drive.foldBox y))) :
    mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
        (Work.Drive.cappingSpaceHomeoProj (Work.Drive.diskPlane Q y)).2) y
      = ((mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
            (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
            (Work.Drive.sqDisk (Work.Drive.foldBox y))).comp
          (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
            (fun y : EuclideanSpace ℝ (Fin 2) =>
              Work.Drive.sqDisk (Work.Drive.foldBox y)) y)) := by
  have hfold : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Work.Drive.foldBox :=
    contDiff_iff_contDiffAt.mpr fun y =>
      contMDiffAt_iff_contDiffAt.mp (Work.Drive.foldBox_contMDiff y)
  have hgdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 2) => Work.Drive.sqDisk (Work.Drive.foldBox y)) :=
    Work.Drive.sqDisk_contDiff.comp hfold
  have hg : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℂ))
      (fun y : EuclideanSpace ℝ (Fin 2) => Work.Drive.sqDisk (Work.Drive.foldBox y)) y :=
    (contMDiffAt_iff_contDiffAt.mpr (hgdiff.contDiffAt)).mdifferentiableAt (by simp)
  have hmain := mfderiv_comp (I := 𝓡 2) (I' := 𝓘(ℝ, ℂ)) (I'' := 𝓡 3)
    (f := fun y : EuclideanSpace ℝ (Fin 2) => Work.Drive.sqDisk (Work.Drive.foldBox y))
    (g := fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2) y hf hg
  have hfun : (fun y : EuclideanSpace ℝ (Fin 2) =>
        (Work.Drive.cappingSpaceHomeoProj (Work.Drive.diskPlane Q y)).2)
      = ((fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2) ∘
          fun y : EuclideanSpace ℝ (Fin 2) => Work.Drive.sqDisk (Work.Drive.foldBox y)) := rfl
  rw [hfun, hmain]

/-- **The immersion of the folded presentation from the immersion of the disk presentation**, in the
unfolded form `Q ∘ sqDisk ∘ foldBox` of `Work.Drive.diskPlane Q`. -/
theorem injective_mfderiv_cls_sqDisk_foldBox (Q : ℂ → Work.Drive.CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2))
    (hf : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
      (Work.Drive.sqDisk (Work.Drive.foldBox y)))
    (hf_inj : Function.Injective (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
      (Work.Drive.sqDisk (Work.Drive.foldBox y))))
    (hg_inj : Function.Injective (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
      (fun y : EuclideanSpace ℝ (Fin 2) => Work.Drive.sqDisk (Work.Drive.foldBox y)) y)) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
      (Work.Drive.cappingSpaceHomeoProj
        (Q (Work.Drive.sqDisk (Work.Drive.foldBox y)))).2) y) := by
  have hmain := mfderiv_cls_diskPlane Q y hf
  simp only [Work.Drive.diskPlane_apply] at hmain
  rw [hmain]
  have hco : ⇑((mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
          (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
          (Work.Drive.sqDisk (Work.Drive.foldBox y))).comp
        (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
          (fun y : EuclideanSpace ℝ (Fin 2) =>
            Work.Drive.sqDisk (Work.Drive.foldBox y)) y))
      = (⇑(mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
            (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
            (Work.Drive.sqDisk (Work.Drive.foldBox y)))
          ∘ ⇑(mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
            (fun y : EuclideanSpace ℝ (Fin 2) =>
              Work.Drive.sqDisk (Work.Drive.foldBox y)) y)) := by
    funext u
    rfl
  rw [hco]
  exact hf_inj.comp hg_inj

/-- The same in the form of the presentation `Work.Drive.diskPlane Q`. -/
theorem injective_mfderiv_cls_diskPlane (Q : ℂ → Work.Drive.CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2))
    (hf : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
      (Work.Drive.sqDisk (Work.Drive.foldBox y)))
    (hf_inj : Function.Injective (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
      (Work.Drive.sqDisk (Work.Drive.foldBox y))))
    (hg_inj : Function.Injective (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
      (fun y : EuclideanSpace ℝ (Fin 2) => Work.Drive.sqDisk (Work.Drive.foldBox y)) y)) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
      (Work.Drive.cappingSpaceHomeoProj (Work.Drive.diskPlane Q y)).2) y) :=
  injective_mfderiv_cls_sqDisk_foldBox Q y hf hf_inj hg_inj

/-- **The range of the class derivative of the folded presentation is that of the disk
presentation**, in the unfolded form `Q ∘ sqDisk ∘ foldBox`.  The second factor of the chain rule is
injective between two `2`-dimensional spaces, hence surjective, so it does not change the range;
consequently the general-position hypothesis `hV` carries over verbatim from the disk presentation to
the folded one. -/
theorem range_mfderiv_cls_sqDisk_foldBox (Q : ℂ → Work.Drive.CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2))
    (hf : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
      (Work.Drive.sqDisk (Work.Drive.foldBox y)))
    (hsurj : Function.Surjective (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
      (fun y : EuclideanSpace ℝ (Fin 2) => Work.Drive.sqDisk (Work.Drive.foldBox y)) y)) :
    (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
        (Work.Drive.cappingSpaceHomeoProj
          (Q (Work.Drive.sqDisk (Work.Drive.foldBox y)))).2) y).range
      = (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
          (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
          (Work.Drive.sqDisk (Work.Drive.foldBox y))).range := by
  have hmain := mfderiv_cls_diskPlane Q y hf
  simp only [Work.Drive.diskPlane_apply] at hmain
  rw [hmain]
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [LinearMap.mem_range] at hz ⊢
    obtain ⟨v, hv⟩ := hz
    refine ⟨(mfderiv (𝓡 2) (𝓘(ℝ, ℂ)) (fun y : EuclideanSpace ℝ (Fin 2) =>
      Work.Drive.sqDisk (Work.Drive.foldBox y)) y) v, ?_⟩
    rw [← hv]
    exact (ContinuousLinearMap.comp_apply _ _ _).symm
  · intro z hz
    rw [LinearMap.mem_range] at hz ⊢
    obtain ⟨u, hu⟩ := hz
    obtain ⟨v, hv⟩ := hsurj u
    refine ⟨v, ?_⟩
    exact (ContinuousLinearMap.comp_apply _ _ _).trans ((congrArg _ hv).trans hu)

/-- The same in the form of the presentation `Work.Drive.diskPlane Q`. -/
theorem range_mfderiv_cls_diskPlane (Q : ℂ → Work.Drive.CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2))
    (hf : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
      (Work.Drive.sqDisk (Work.Drive.foldBox y)))
    (hsurj : Function.Surjective (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
      (fun y : EuclideanSpace ℝ (Fin 2) => Work.Drive.sqDisk (Work.Drive.foldBox y)) y)) :
    (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
        (Work.Drive.cappingSpaceHomeoProj (Work.Drive.diskPlane Q y)).2) y).range
      = (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
          (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
          (Work.Drive.sqDisk (Work.Drive.foldBox y))).range :=
  range_mfderiv_cls_sqDisk_foldBox Q y hf hsurj

/-! ## The square-to-disk parametrisation is an immersion on the open square -/

/-- **The `mfderiv` form of the square-to-disk immersion**, from the delegated
`Work.Drive.injective_fderiv_sqDisk_foldBox` (the map is between model spaces, so `mfderiv` is
`fderiv`). -/
theorem inj_mfderiv_sqDisk_foldBox (y : EuclideanSpace ℝ (Fin 2))
    (h0 : y 0 ∈ Set.Ioo (0 : ℝ) 1) (h1 : y 1 ∈ Set.Ioo (0 : ℝ) 1) :
    Function.Injective (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
      (fun y : EuclideanSpace ℝ (Fin 2) => Work.Drive.sqDisk (Work.Drive.foldBox y)) y) := by
  rw [mfderiv_eq_fderiv]
  exact Work.Drive.injective_fderiv_sqDisk_foldBox y h0 h1

/-- The same map is also **surjective** there: it is injective between two `2`-dimensional real
spaces. -/
theorem surj_mfderiv_sqDisk_foldBox (y : EuclideanSpace ℝ (Fin 2))
    (h0 : y 0 ∈ Set.Ioo (0 : ℝ) 1) (h1 : y 1 ∈ Set.Ioo (0 : ℝ) 1) :
    Function.Surjective (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
      (fun y : EuclideanSpace ℝ (Fin 2) => Work.Drive.sqDisk (Work.Drive.foldBox y)) y) := by
  have hinj := inj_mfderiv_sqDisk_foldBox y h0 h1
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = Module.finrank ℝ ℂ := by simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) hfin).mp hinj

/-- **The immersion hypothesis `hc` for the folded presentation, from the disk presentation and the
open-square hypotheses.**  This is the form in which the geometric input (i) plugs in: the caller only
has to prove that the *disk presentation* `Q` is an immersion at `sqDisk (foldBox y)`, the square being
in the open square. -/
theorem injective_mfderiv_cls_diskPlane_of_openSquare (Q : ℂ → Work.Drive.CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2))
    (h0 : y 0 ∈ Set.Ioo (0 : ℝ) 1) (h1 : y 1 ∈ Set.Ioo (0 : ℝ) 1)
    (hf : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
      (Work.Drive.sqDisk (Work.Drive.foldBox y)))
    (hf_inj : Function.Injective (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
      (Work.Drive.sqDisk (Work.Drive.foldBox y)))) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
      (Work.Drive.cappingSpaceHomeoProj (Work.Drive.diskPlane Q y)).2) y) :=
  injective_mfderiv_cls_diskPlane Q y hf hf_inj (inj_mfderiv_sqDisk_foldBox y h0 h1)

/-- **The general-position hypothesis `hV` transfers from the disk presentation to the folded one.** -/
theorem range_mfderiv_cls_diskPlane_of_openSquare (Q : ℂ → Work.Drive.CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2))
    (h0 : y 0 ∈ Set.Ioo (0 : ℝ) 1) (h1 : y 1 ∈ Set.Ioo (0 : ℝ) 1)
    (hf : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 3)
      (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
      (Work.Drive.sqDisk (Work.Drive.foldBox y))) :
    (mfderiv (𝓡 2) (𝓡 3) (fun y : EuclideanSpace ℝ (Fin 2) =>
        (Work.Drive.cappingSpaceHomeoProj (Work.Drive.diskPlane Q y)).2) y).range
      = (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
          (fun z : ℂ => (Work.Drive.cappingSpaceHomeoProj (Q z)).2)
          (Work.Drive.sqDisk (Work.Drive.foldBox y))).range :=
  range_mfderiv_cls_diskPlane Q y hf (surj_mfderiv_sqDisk_foldBox y h0 h1)

end

end Work.Drive
