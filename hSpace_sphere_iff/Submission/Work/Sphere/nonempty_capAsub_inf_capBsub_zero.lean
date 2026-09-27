/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The intersection of the two pieces of the cover is nonempty in degree `0`

The Mayer–Vietoris cover of the small complex of `S^{n+2}` by the two caps intersected with the
small simplices has a nonempty intersection of `0`-simplices: the doubly punctured sphere is
nonempty, so it carries a point, and the constant `0`-simplex at that point is a small simplex
lying in both caps.  This is the little input that makes the `0`-th cohomology of the
intersection a non-vacuous object.
-/
import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Sphere.Suspension
import Submission.Work.Sphere.sphere_doublePunctured_homotopyEquiv

namespace Work.Sphere

open CategoryTheory Simplicial Opposite
open Submission.Sphere

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

/-- A point of `S^{n+2}` lying in neither of the two poles, i.e. the first basis vector. -/
private def goodPt (n : ℕ) : Sph (n+2) :=
  ⟨EuclideanSpace.single (0 : Fin (n+3)) 1,
    by rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]; norm_num⟩

private lemma goodPt_mem_capPlus (n : ℕ) : goodPt n ∈ capPlus (n+1) := by
  intro h
  have h2 : (EuclideanSpace.single (0 : Fin (n+3)) (1:ℝ)).ofLp
      = (pole (n+1+1)).ofLp := congrArg WithLp.ofLp h
  have h3 := congrFun h2 (0 : Fin (n+3))
  rw [PiLp.single_apply] at h3
  simp [Submission.Sphere.pole] at h3

private lemma goodPt_mem_capMinus (n : ℕ) : goodPt n ∈ capMinus (n+1) := by
  intro h
  have h2 : (EuclideanSpace.single (0 : Fin (n+3)) (1:ℝ)).ofLp
      = (-pole (n+1+1)).ofLp := congrArg WithLp.ofLp h
  have h3 := congrFun h2 (0 : Fin (n+3))
  rw [PiLp.single_apply] at h3
  simp [Submission.Sphere.pole] at h3

/-- The constant `0`-simplex at the point `goodPt n`, viewed as a singular simplex of `S^{n+2}`. -/
private def goodSimplex (n : ℕ) :
    (TopCat.toSSet.obj (Sph (n+2))).obj (op (SimplexCategory.mk 0)) :=
  (TopCat.toSSetObjEquivT (Sph (n+2)) (op (SimplexCategory.mk 0))).symm
    (ContinuousMap.const (stdSimplex ℝ (Fin 1)) (goodPt n))

private lemma goodSimplex_mem_capPlusSub (n : ℕ) :
    goodSimplex n ∈ (capPlusSub (n+1)).obj (op (SimplexCategory.mk 0)) := by
  rw [Submission.Cohomology.mem_singIn_iff]
  intro t
  have h : TopCat.toSSetObjEquivT (Sph (n+2)) (op (SimplexCategory.mk 0)) (goodSimplex n)
      = ContinuousMap.const (stdSimplex ℝ (Fin 1)) (goodPt n) :=
    Equiv.apply_symm_apply _ _
  rw [h, ContinuousMap.const_apply]
  exact goodPt_mem_capPlus n

private lemma goodSimplex_mem_capMinusSub (n : ℕ) :
    goodSimplex n ∈ (capMinusSub (n+1)).obj (op (SimplexCategory.mk 0)) := by
  rw [Submission.Cohomology.mem_singIn_iff]
  intro t
  have h : TopCat.toSSetObjEquivT (Sph (n+2)) (op (SimplexCategory.mk 0)) (goodSimplex n)
      = ContinuousMap.const (stdSimplex ℝ (Fin 1)) (goodPt n) :=
    Equiv.apply_symm_apply _ _
  rw [h, ContinuousMap.const_apply]
  exact goodPt_mem_capMinus n

theorem nonempty_capAsub_inf_capBsub_zero (n : ℕ) :
    Nonempty (((Submission.Sphere.capAsub (n+1)) ⊓ (Submission.Sphere.capBsub (n+1)) :
      (Submission.Sphere.smallC (n+1)).Subcomplex).obj (Opposite.op (SimplexCategory.mk 0))) := by
  refine ⟨⟨goodSimplex n, Or.inl (goodSimplex_mem_capPlusSub n)⟩, ?_, ?_⟩
  · show goodSimplex n ∈ (capPlusSub (n+1)).obj (op (SimplexCategory.mk 0))
    exact goodSimplex_mem_capPlusSub n
  · show goodSimplex n ∈ (capMinusSub (n+1)).obj (op (SimplexCategory.mk 0))
    exact goodSimplex_mem_capMinusSub n

end

end Work.Sphere
