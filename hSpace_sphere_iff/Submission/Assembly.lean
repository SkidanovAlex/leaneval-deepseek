/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The spheres `S⁰, S¹, S³, S⁷` are H-spaces

This file assembles the reverse direction of Adams' theorem: for `n ∈ {0, 1, 3, 7}` the Euclidean
sphere `Sⁿ ⊆ ℝⁿ⁺¹` carries an H-space structure.  The structure is transported, along a
`LinearIsometryEquiv`, from the unit sphere of the normed division algebra `ℝ` (`n = 0`), `ℂ`
(`n = 1`), `ℍ` (`n = 3`) and from the unit sphere of the octonions `𝕆` (`n = 7`), cf.
`Submission/Work/Octonion/Basic.lean`.

Together with `Submission.hSpace_sphere_iff` this computes the set of dimensions in which the
H-space structure exists, the hard half being Adams' Hopf-invariant-one theorem.
-/
import Mathlib
import Submission.Work.HSpace.Basic
import Submission.Work.Octonion.Sphere
import Submission.Work.Octonion.isometry_equiv_euclidean

open scoped Quaternion

namespace Submission

/-- `ℝ` as the one-dimensional Euclidean space (as a normed space over itself). -/
noncomputable def realEuclideanOne : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap :=
        { toFun := fun x => WithLp.toLp 2 (fun _ : Fin 1 => x)
          map_add' := by intro a b; apply WithLp.ofLp_injective; ext i; simp
          map_smul' := by intro a b; apply WithLp.ofLp_injective; ext i; simp }
      norm_map' := by
        intro x
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (by positivity)]
        simp }
    (fun y => ⟨WithLp.ofLp y 0, by
      apply WithLp.ofLp_injective
      ext i
      simp [Subsingleton.elim i 0]⟩)

/-- `S⁰` is an H-space (the two-point space `{±1}` is the group of units of `ℝ`). -/
theorem hSpace_sphere_zero :
    Nonempty (HSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) :=
  hSpace_transport (sphereCongrLIE realEuclideanOne) ⟨inferInstance⟩

/-- `S¹` is an H-space (the unit complex numbers form a topological group). -/
theorem hSpace_sphere_one :
    Nonempty (HSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
  hSpace_transport (sphereCongrLIE Complex.orthonormalBasisOneI.repr) ⟨inferInstance⟩

/-- `S³` is an H-space (the unit quaternions form a topological group). -/
theorem hSpace_sphere_three :
    Nonempty (HSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :=
  hSpace_transport (sphereCongrLIE Quaternion.linearIsometryEquivTuple) ⟨inferInstance⟩

/-- `S⁷` is an H-space: the unit octonions form an H-space (they are not a group, the octonion
multiplication being non-associative). -/
theorem hSpace_sphere_seven :
    Nonempty (HSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1)) := by
  have h : Nonempty (HSpace (Metric.sphere (0 : Submission.Octonion) 1)) := ⟨inferInstance⟩
  obtain ⟨e⟩ := Work.Octonion.isometry_equiv_euclidean
  exact hSpace_transport (sphereCongrLIE e) h

/-- **The reverse direction of Adams' theorem.** For `n = 0, 1, 3, 7` the sphere `Sⁿ` carries an
H-space structure: the unit spheres of `ℝ`, `ℂ`, `ℍ` are topological groups and the unit sphere of
the octonions is an H-space. -/
theorem hSpace_sphere_of_mem (n : ℕ) (h : n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 7) :
    Nonempty (HSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
  rcases h with rfl | rfl | rfl | rfl
  · exact hSpace_sphere_zero
  · exact hSpace_sphere_one
  · exact hSpace_sphere_three
  · exact hSpace_sphere_seven

end Submission
