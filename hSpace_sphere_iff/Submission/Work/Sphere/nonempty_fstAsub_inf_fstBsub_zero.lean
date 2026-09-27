import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Sphere.ProdSetup

namespace Work.Sphere

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- A point of `S^{a+1}` lying in neither pole: the first standard basis vector. -/
private def goodPt (a : ℕ) : Submission.Sphere.Sph (a+1) :=
  ⟨EuclideanSpace.single (0 : Fin (a+2)) 1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, PiLp.norm_single]; norm_num⟩

private lemma goodPt_mem_capPlus (a : ℕ) :
    goodPt a ∈ Submission.Sphere.capPlus a := by
  intro h
  have h2 : (EuclideanSpace.single (0 : Fin (a+2)) (1:ℝ)).ofLp
      = (Submission.Sphere.pole (a+1)).ofLp := congrArg WithLp.ofLp h
  have h3 := congrFun h2 (0 : Fin (a+2))
  rw [PiLp.single_apply] at h3
  simp [Submission.Sphere.pole] at h3

private lemma goodPt_mem_capMinus (a : ℕ) :
    goodPt a ∈ Submission.Sphere.capMinus a := by
  intro h
  have h2 : (EuclideanSpace.single (0 : Fin (a+2)) (1:ℝ)).ofLp
      = (-Submission.Sphere.pole (a+1)).ofLp := congrArg WithLp.ofLp h
  have h3 := congrFun h2 (0 : Fin (a+2))
  rw [PiLp.single_apply] at h3
  simp [Submission.Sphere.pole] at h3

/-- The constant `0`-simplex of `S^{a+1} × Y` at a point `p`. -/
private def constSimplex (a : ℕ) (Y : TopCat.{0})
    (p : ↥(TopProd (Submission.Sphere.Sph (a+1)) Y)) :
    (TopCat.toSSet.obj (TopProd (Submission.Sphere.Sph (a+1)) Y)).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  (TopCat.toSSetObjEquivT (TopProd (Submission.Sphere.Sph (a+1)) Y)
      (Opposite.op (SimplexCategory.mk 0))).symm
    (ContinuousMap.const (stdSimplex ℝ (Fin 1)) p)

/-- The constant `0`-simplex at `p` lies in the subcomplex of simplices whose first coordinate
lies in `W`, as soon as `p.1 ∈ W`. -/
private lemma constSimplex_mem (a : ℕ) (Y : TopCat.{0})
    (p : ↥(TopProd (Submission.Sphere.Sph (a+1)) Y))
    (W : Set (Submission.Sphere.Sph (a+1))) (hp : p.1 ∈ W) :
    constSimplex a Y p ∈ (fstSub (Submission.Sphere.Sph (a+1)) Y W).obj
      (Opposite.op (SimplexCategory.mk 0)) := by
  rw [Submission.Cohomology.mem_singIn_iff]
  intro t
  have h : TopCat.toSSetObjEquivT (TopProd (Submission.Sphere.Sph (a+1)) Y)
      (Opposite.op (SimplexCategory.mk 0)) (constSimplex a Y p)
      = ContinuousMap.const (stdSimplex ℝ (Fin 1)) p :=
    Equiv.apply_symm_apply _ _
  rw [h, ContinuousMap.const_apply]
  exact hp

theorem nonempty_fstAsub_inf_fstBsub_zero (a : ℕ) (Y : TopCat.{0}) [Nonempty ↥Y] :
    Nonempty ((Work.Sphere.fstAsub (Submission.Sphere.Sph (a+1)) Y (Submission.Sphere.capPlus a)
        (Submission.Sphere.capMinus a) ⊓
      Work.Sphere.fstBsub (Submission.Sphere.Sph (a+1)) Y (Submission.Sphere.capPlus a)
        (Submission.Sphere.capMinus a)).obj (Opposite.op (SimplexCategory.mk 0))) := by
  obtain ⟨y⟩ := (inferInstance : Nonempty ↥Y)
  let p : ↥(TopProd (Submission.Sphere.Sph (a+1)) Y) := (goodPt a, y)
  have hp1 : p.1 ∈ Submission.Sphere.capPlus a := goodPt_mem_capPlus a
  have hp2 : p.1 ∈ Submission.Sphere.capMinus a := goodPt_mem_capMinus a
  have h1 : constSimplex a Y p ∈ (fstSub (Submission.Sphere.Sph (a+1)) Y
      (Submission.Sphere.capPlus a)).obj (Opposite.op (SimplexCategory.mk 0)) :=
    constSimplex_mem a Y p _ hp1
  have h2 : constSimplex a Y p ∈ (fstSub (Submission.Sphere.Sph (a+1)) Y
      (Submission.Sphere.capMinus a)).obj (Opposite.op (SimplexCategory.mk 0)) :=
    constSimplex_mem a Y p _ hp2
  refine ⟨⟨constSimplex a Y p, Or.inl h1⟩, ?_, ?_⟩
  · exact h1
  · exact h2

end

end Work.Sphere
