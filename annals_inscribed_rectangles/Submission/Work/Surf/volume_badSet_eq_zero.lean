import Mathlib
import Submission.Work.Surf.GoodRayDefs

/-!
# The set of bad directions is null

`Work.Surf.badSet F = tangentCone F ∪ cornerLines F` is the set of directions that a good ray has to
avoid: the radial directions of the boundary curve `t ↦ F (sqBoxLoop t)` at the critical times, and
the four lines through the corner values of the square.

Both parts are Lebesgue null.

* The tangent cone is the image of the critical set of the map `φ : ℝ × ℝ → ℝ × ℝ`,
  `φ (t, c) = c • F (sqBoxLoop t)`.  A direct computation gives
  `det (fderiv ℝ φ (t, c)) = - c * cross2 (F (sqBoxLoop t)) (deriv (F ∘ sqBoxLoop) t)`, which
  vanishes on `critTimes F × Set.univ`; the equal-dimension case of Sard's theorem
  (`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`) then gives the result.
  (The boundary curve `t ↦ F (sqBoxLoop t)` is differentiable at every `t ∉ {1, 2, 3}`, which is
  exactly the condition appearing in `critTimes`.)

* `cornerLines F` is a finite union of lines through the origin; each line is contained in the image
  of the rank one linear map `(x, y) ↦ x • v`, whose derivative has vanishing determinant.
-/

namespace Work.Surf

open MeasureTheory
open Work.Drive

open scoped Topology

noncomputable section

/-- A line through the origin in `ℝ × ℝ` is a Lebesgue null set. -/
lemma volume_range_smul_eq_zero (v : ℝ × ℝ) :
    MeasureTheory.volume (Set.range (fun a : ℝ => a • v)) = 0 := by
  have himg : MeasureTheory.volume ((fun p : ℝ × ℝ => p.1 • v) '' Set.univ) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume) (s := Set.univ)
      (f := fun p : ℝ × ℝ => p.1 • v)
      (f' := fun _ => (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v) ?_ ?_
    · intro p _
      exact (ContinuousLinearMap.hasFDerivAt
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v)).hasFDerivWithinAt
    · intro p _
      have hker : ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v :
          (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).ker ≠ ⊥ := by
        rw [Submodule.ne_bot_iff]
        refine ⟨(0, 1), ?_, by simp⟩
        simp [LinearMap.mem_ker]
      have hd : LinearMap.det (((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight v :
          (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)).toLinearMap) = 0 :=
        (LinearMap.det_eq_zero_iff_ker_ne_bot (f := _)).mpr hker
      simpa [ContinuousLinearMap.det] using hd
  exact measure_mono_null
    (by rintro y ⟨a, rfl⟩; exact ⟨(a, 0), Set.mem_univ _, rfl⟩) himg

/-- The derivative of the parametrisation `φ (t, c) = c • F (sqBoxLoop t)` of the tangent cone at a
point whose `t`-coordinate is not one of the corner parameters. -/
lemma hasFDerivAt_tanParam (F : ℝ × ℝ → ℝ × ℝ) (hF : ContDiff ℝ 1 F) {t c : ℝ}
    (h1 : t ≠ 1) (h2 : t ≠ 2) (h3 : t ≠ 3) :
    HasFDerivAt (fun p : ℝ × ℝ => p.2 • F (sqBoxLoop p.1))
      (c • ((fderiv ℝ (fun s : ℝ => F (sqBoxLoop s)) t).comp
          (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F (sqBoxLoop t))) (t, c) := by
  have hg : DifferentiableAt ℝ (fun s : ℝ => F (sqBoxLoop s)) t :=
    differentiableAt_boundaryCurve F hF h1 h2 h3
  have hc : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (t, c) :=
    ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hf : HasFDerivAt (fun p : ℝ × ℝ => F (sqBoxLoop p.1))
      ((fderiv ℝ (fun s : ℝ => F (sqBoxLoop s)) t).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) (t, c) :=
    HasFDerivAt.comp (x := (t, c)) (g := fun s : ℝ => F (sqBoxLoop s))
      (f := fun p : ℝ × ℝ => p.1) (f' := ContinuousLinearMap.fst ℝ ℝ ℝ)
      (g' := fderiv ℝ (fun s : ℝ => F (sqBoxLoop s)) t)
      hg.hasFDerivAt (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ ℝ ℝ))
  exact hc.smul hf

/-- The derivative of `φ` is singular at every critical time. -/
lemma det_fderiv_tanParam_eq_zero (F : ℝ × ℝ → ℝ × ℝ) (hF : ContDiff ℝ 1 F) {t c : ℝ}
    (ht : t ∈ critTimes F) :
    (fderiv ℝ (fun p : ℝ × ℝ => p.2 • F (sqBoxLoop p.1)) (t, c)).det = 0 := by
  obtain ⟨h1, h2, h3, hcr⟩ := ht
  have hφ := hasFDerivAt_tanParam F hF h1 h2 h3 (t := t) (c := c)
  rw [hφ.fderiv]
  set A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    c • ((fderiv ℝ (fun s : ℝ => F (sqBoxLoop s)) t).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F (sqBoxLoop t)) with hA
  -- the value of `A` on an arbitrary vector
  have key : ∀ dt dc : ℝ, A (dt, dc)
      = c • ((fderiv ℝ (fun s : ℝ => F (sqBoxLoop s)) t) dt) + dc • F (sqBoxLoop t) := by
    intro dt dc
    simp [hA, ContinuousLinearMap.smulRight_apply]
  -- `A` has a nontrivial kernel because `F (sqBoxLoop t)` and the derivative of the curve are
  -- linearly dependent, `t` being a critical time
  have hker : A.ker ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    by_cases hg0 : F (sqBoxLoop t) = 0
    · have hA0 : A (0, 1) = 0 := by
        rw [key 0 1]
        simp [hg0]
      exact ⟨(0, 1), LinearMap.mem_ker.mpr hA0, by simp⟩
    · obtain ⟨μ, hμ⟩ := Work.Drive.exists_smul_of_cross2_eq_zero hg0 hcr
      have hA1 : A (1, -(c * μ)) = 0 := by
        rw [key 1 (-(c * μ)), fderiv_apply_one_eq_deriv, hμ]
        simp [smul_smul]
      exact ⟨(1, -(c * μ)), LinearMap.mem_ker.mpr hA1, by simp⟩
  have hd : LinearMap.det A.toLinearMap = 0 :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot (f := A.toLinearMap)).mpr hker
  simpa [ContinuousLinearMap.det] using hd

theorem volume_badSet_eq_zero (F : ℝ × ℝ → ℝ × ℝ) (hF : ContDiff ℝ 1 F) :
    MeasureTheory.volume (Work.Surf.badSet F) = 0 := by
  -- the four corner lines
  have hcorner : MeasureTheory.volume (cornerLines F) = 0 := by
    show MeasureTheory.volume
      (⋃ j : Fin 4, Set.range (fun a : ℝ => a • cornerVal F j)) = 0
    exact measure_iUnion_null (fun j => volume_range_smul_eq_zero _)
  -- the tangent cone, by the equal-dimension Sard lemma
  have htan : MeasureTheory.volume (tangentCone F) = 0 := by
    show MeasureTheory.volume
      ((fun p : ℝ × ℝ => p.2 • F (sqBoxLoop p.1)) '' (critTimes F ×ˢ Set.univ)) = 0
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
      (s := critTimes F ×ˢ Set.univ)
      (f := fun p : ℝ × ℝ => p.2 • F (sqBoxLoop p.1))
      (f' := fun p => fderiv ℝ (fun p : ℝ × ℝ => p.2 • F (sqBoxLoop p.1)) p) ?_ ?_
    · rintro ⟨t, c⟩ hp
      have hφ := hasFDerivAt_tanParam F hF hp.1.1 hp.1.2.1 hp.1.2.2.1 (t := t) (c := c)
      rw [hφ.fderiv]
      exact hφ.hasFDerivWithinAt
    · rintro ⟨t, c⟩ hp
      exact det_fderiv_tanParam_eq_zero F hF hp.1
  show MeasureTheory.volume (tangentCone F ∪ cornerLines F) = 0
  exact measure_union_null htan hcorner

end

end Work.Surf
