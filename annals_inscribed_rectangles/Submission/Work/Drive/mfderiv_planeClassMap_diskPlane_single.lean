import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.cappingCharted
import Submission.Work.Drive.classTripleRegular
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.diskPlane_mfderiv
import Submission.Work.Drive.injective_fderiv_sqDisk_foldBox
import Submission.Work.Drive.chartGenericity

/-!
# The fold degeneracy of the class map of a disk presentation

`Work.Drive.planeClassMap (Work.Drive.diskPlane Q) = cls ∘ Q ∘ sqDisk ∘ foldBox` is the *folded*
presentation of the plane of a chart `Q`, and the fold `foldBox` is symmetric about every point
`y` with `y i ∈ {0,1}` in the `i`-th coordinate.  Consequently the *directional derivative* of the
class map in the direction `eᵢ` vanishes at such a `y`:

> `mfderiv (planeClassMap (diskPlane Q)) y (EuclideanSpace.single i 1) = 0` for `y i = 0` or `y i = 1`.

This is the geometric input behind the *fold hypotheses* of the ends-clause genericity: the face
obstruction of the box-reparametrisation route (`ENCODED_FAMILY_STATUS.md` §2) is repaired exactly
because the direction a box self-diffeomorphism loses at `y i ∈ {0,1}` is a direction the folded
presentation already kills.

The file was **deleted and restored** (session of the `orderSplit_model` lane): the three proof bricks
`mfd_foldFun_neg`, `mfd_foldFun_symm_zero`, `mfd_foldFun_symm_one`,
`mfd_foldBox_add_single_eq_sub`, `fderiv_apply_eq_zero_of_reflect_symm` and the main theorem are the
recovery of the (verified) proof of the delegated lemma `Drive/mfderiv_planeClassMap_diskPlane_single`;
the deleted module is reconstructed here from the recorded statement and proof outline.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-! ## 1. The reflection symmetry of the fold -/

/-- The fold `foldFun x = (1 - cos (π x))/2` is even. -/
lemma mfd_foldFun_neg (t : ℝ) : foldFun (-t) = foldFun t := by
  simp [foldFun]

/-- The fold is symmetric about `0`. -/
lemma mfd_foldFun_symm_zero (t : ℝ) : foldFun (0 + t) = foldFun (0 - t) := by
  simp [mfd_foldFun_neg]

/-- The fold is symmetric about `1`. -/
lemma mfd_foldFun_symm_one (t : ℝ) : foldFun (1 + t) = foldFun (1 - t) := by
  have h1 : foldFun (1 + t) = 1 - foldFun t := by
    rw [show (1 : ℝ) + t = 1 - (-t) by ring, foldFun_symm, mfd_foldFun_neg]
  rw [h1, foldFun_symm]

/-- The scalar reflection identity of the fold at `0` and `1`. -/
lemma foldFun_reflect_of_mem (z : ℝ) (hz : z = 0 ∨ z = 1) (t : ℝ) :
    foldFun (z + t) = foldFun (z - t) := by
  rcases hz with h | h
  · rw [h]; exact mfd_foldFun_symm_zero t
  · rw [h]; exact mfd_foldFun_symm_one t

/-- **The fold is symmetric about the affine line through `y` in the direction `eᵢ` whenever
`y i ∈ {0,1}`**: the folded square coordinates do not see the sign of `t`. -/
theorem mfd_foldBox_add_single_eq_sub (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2)
    (hy : y i = 0 ∨ y i = 1) (t : ℝ) :
    foldBox (y + t • EuclideanSpace.single i (1 : ℝ))
      = foldBox (y - t • EuclideanSpace.single i (1 : ℝ)) := by
  have hy' : y.ofLp i = 0 ∨ y.ofLp i = 1 := hy
  have key : foldFun (y.ofLp i + t) = foldFun (y.ofLp i - t) :=
    foldFun_reflect_of_mem (y.ofLp i) hy' t
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [foldBox, mk2, PiLp.toLp_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      PiLp.single_apply, WithLp.ofLp_toLp, smul_eq_mul, mul_one, mul_zero, add_zero, sub_zero,
      reduceIte, one_ne_zero, zero_ne_one, if_true, if_false]
  · simpa using key
  · simp
  · simp
  · simpa using key

/-! ## 2. The derivative of a function symmetric about a point -/

/-- **A function reflection-symmetric about `x` in the direction `w` has vanishing directional
derivative there.** -/
theorem fderiv_apply_eq_zero_of_reflect_symm {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] (F : E → Z) (x w : E)
    (hF : DifferentiableAt ℝ F x) (h : ∀ t : ℝ, F (x + t • w) = F (x - t • w)) :
    fderiv ℝ F x w = 0 := by
  have hd1 : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have hd2 : HasDerivAt (fun t : ℝ => x - t • w) (-w) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_sub x
  have hFx : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • w) := by
    simpa using hF.hasFDerivAt
  have hFy : HasFDerivAt F (fderiv ℝ F x) (x - (0 : ℝ) • w) := by
    simpa using hF.hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => F (x + t • w)) ((fderiv ℝ F x) w) 0 := by
    simpa [Function.comp_def] using hFx.comp_hasDerivAt 0 hd1
  have h2 : HasDerivAt (fun t : ℝ => F (x + t • w)) (-((fderiv ℝ F x) w)) 0 := by
    rw [show (fun t : ℝ => F (x + t • w)) = fun t => F (x - t • w) from funext h]
    simpa [Function.comp_def] using hFy.comp_hasDerivAt 0 hd2
  have heq : (fderiv ℝ F x) w = -((fderiv ℝ F x) w) := h1.unique h2
  have hsum : (fderiv ℝ F x) w + (fderiv ℝ F x) w = 0 := by
    nth_rewrite 1 [heq]
    exact neg_add_cancel _
  have htwo : (2 : ℝ) • ((fderiv ℝ F x) w) = 0 := by rw [two_smul, hsum]
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-! ## 3. The fold degeneracy of the class map -/

/-- **The class map of a folded disk presentation is critical in the fold directions.** -/
theorem mfderiv_planeClassMap_diskPlane_single (Q : ℂ → Work.Drive.CappingSpace)
    (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) (hy : y i = 0 ∨ y i = 1) :
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
      (Work.Drive.planeClassMap (Work.Drive.diskPlane Q)) y
      (EuclideanSpace.single i (1 : ℝ)) = 0 := by
  intro hQ
  -- the fold is differentiable and its derivative kills the fold direction
  have hfold_diff : DifferentiableAt ℝ foldBox y :=
    (contMDiffAt_iff_contDiffAt.mp (foldBox_contMDiff y)).differentiableAt (by simp)
  have hbox : fderiv ℝ foldBox y (EuclideanSpace.single i (1 : ℝ)) = 0 :=
    fderiv_apply_eq_zero_of_reflect_symm foldBox y (EuclideanSpace.single i (1 : ℝ)) hfold_diff
      (mfd_foldBox_add_single_eq_sub y i hy)
  -- the square-to-disk map therefore kills it too
  have hsq : DifferentiableAt ℝ sqDisk (foldBox y) :=
    sqDisk_contDiff.contDiffAt.differentiableAt (by simp)
  have hg : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox z)) y
      (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    change fderiv ℝ (sqDisk ∘ foldBox) y (EuclideanSpace.single i (1 : ℝ)) = 0
    rw [fderiv_comp y hsq hfold_diff, ContinuousLinearMap.comp_apply, hbox, map_zero]
  have hinner : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℂ)
      (fun z : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox z)) y
      (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    rw [mfderiv_eq_fderiv]
    exact hg
  -- the class map is the composite with the (differentiable) class projection
  have hf := mdifferentiableAt_cls_of_contMDiff_cplx hQ (sqDisk (foldBox y))
  have hchain := mfderiv_cls_diskPlane Q y hf
  simp only [Work.Drive.diskPlane_apply] at hchain
  change mfderiv (𝓡 2) (𝓡 3)
      (fun y : EuclideanSpace ℝ (Fin 2) =>
        (cappingSpaceHomeoProj (Q (sqDisk (foldBox y)))).2) y
      (EuclideanSpace.single i (1 : ℝ)) = 0
  rw [hchain]
  -- `(A ∘SL B) v` unfolds definitionally to `A (B v)`, where `B v = 0` and `A 0 = 0`
  exact Eq.mpr (congrArg (fun a =>
        (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3) (fun z : ℂ => (cappingSpaceHomeoProj (Q z)).2)
          (sqDisk (foldBox y))) a = 0) hinner)
    (Eq.mpr (congrArg (fun b => b = 0) (map_zero (mfderiv (𝓘(ℝ, ℂ)) (𝓡 3)
        (fun z : ℂ => (cappingSpaceHomeoProj (Q z)).2) (sqDisk (foldBox y)))))
      (Eq.refl 0))

end

end Work.Drive
