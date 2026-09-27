import Mathlib
import Submission.Work.Sphere.Basic

/-!
# `S⁰` is a two-point space

`S⁰ = Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1` is the unit sphere of `ℝ¹`, hence the
two-point space `{1, -1}`, i.e. `{polePt 0, negPolePt 0}`.  This file records that fact: every
point of `S⁰` is one of the two poles.

The proof is elementary: a point `x` of `S⁰` is a vector `v : ℝ¹` with `‖v‖ = 1`.  Since `Fin 1`
is a subsingleton, `‖v‖ = |v 0|`, so `v 0 = ±1`, and a vector of `ℝ¹` is determined by its single
coordinate.
-/

namespace Work.Sphere

open Submission.Sphere

/-- In `ℝ¹` the norm is the absolute value of the single coordinate. -/
private lemma norm_eq_abs_coord (v : EuclideanSpace ℝ (Fin 1)) : ‖v‖ = |v 0| := by
  rw [EuclideanSpace.norm_eq]
  simp
  rw [Real.sqrt_sq_eq_abs]

theorem SphZeroTwoPoints (x : Submission.Sphere.Sph 0) :
    x = Submission.Sphere.polePt 0 ∨ x = Submission.Sphere.negPolePt 0 := by
  have hnorm : ‖(x : EuclideanSpace ℝ (Fin 1))‖ = 1 := by
    have h := x.2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at h
    exact h
  have habs : |(x : EuclideanSpace ℝ (Fin 1)) 0| = 1 := by
    rw [← norm_eq_abs_coord]; exact hnorm
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h1 | h1
  · left
    have hv : (x : EuclideanSpace ℝ (Fin 1)) = pole 0 := by
      apply PiLp.ext
      intro i
      rw [Fin.fin_one_eq_zero i]
      simp [pole, Fin.last_zero, h1]
    exact Subtype.ext hv
  · right
    have hv : (x : EuclideanSpace ℝ (Fin 1)) = -pole 0 := by
      apply PiLp.ext
      intro i
      rw [Fin.fin_one_eq_zero i]
      simp [pole, Fin.last_zero, h1]
    exact Subtype.ext hv

end Work.Sphere
