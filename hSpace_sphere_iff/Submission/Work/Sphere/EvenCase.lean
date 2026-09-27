/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The even case of Adams' theorem

For even `n ≥ 2` the sphere `Sⁿ` is not an H-space.  This file assembles the three inputs:

* the cohomology of the spheres (`sphere_shift`, `subsingleton_H_singSph`,
  `exists_ne_zero_H_singSph`),
* the dimension input `H_dim_sph_prod` (the two projection pullbacks span `H^n(Sⁿ×Sⁿ; ℚ)`),
* the H-space contradiction `Work.HSpace.no_hSpace_sph_even`.
-/
import Mathlib
import Submission.Work.Sphere.Values
import Submission.Work.Sphere.H_dim_sph_prod
import Submission.Work.HSpace.no_hSpace_sph_even

open CategoryTheory Simplicial Opposite
open SSet

namespace Submission.Sphere

open Submission.Cohomology

noncomputable section

set_option maxHeartbeats 1000000

/-- **The even case of Adams' theorem** (auxiliary form, with the dimension input as a
hypothesis): for even `n ≥ 2`, the sphere `Sⁿ` is not an H-space. -/
theorem not_hSpace_sphere_even_aux (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (hdim : LinearMap.range (Submission.Cohomology.H.map ℚ
          (CategoryTheory.SemiCartesianMonoidalCategory.fst (singSph n) (singSph n)) n)
        ⊔ LinearMap.range (Submission.Cohomology.H.map ℚ
          (CategoryTheory.SemiCartesianMonoidalCategory.snd (singSph n) (singSph n)) n) = ⊤) :
    ¬ Nonempty (HSpace (↥(Sph n))) := by
  intro h
  obtain ⟨e⟩ := Work.Sphere.sphere_top n (by omega)
  have hx : e.symm 1 ≠ 0 := by
    intro h0
    have h1 : (1 : ℚ) = 0 := by rw [← e.apply_symm_apply 1, h0, map_zero]
    exact one_ne_zero h1
  exact Work.HSpace.no_hSpace_sph_even n hn heven hdim
    (Work.Sphere.sphere_subsingleton n (2 * n) (by omega) (by omega)) (e.symm 1) hx
    (Classical.choice h)

/-- **The even case of Adams' theorem**: for even `n ≥ 2`, the sphere
`Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1` is not an H-space.  (Auxiliary form: the
dimension input `Work.Sphere.H_dim_sph_prod n hn` is supplied by the caller.) -/
theorem not_hSpace_sphere_even (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (hdim : LinearMap.range (Submission.Cohomology.H.map ℚ
          (CategoryTheory.SemiCartesianMonoidalCategory.fst (singSph n) (singSph n)) n)
        ⊔ LinearMap.range (Submission.Cohomology.H.map ℚ
          (CategoryTheory.SemiCartesianMonoidalCategory.snd (singSph n) (singSph n)) n) = ⊤) :
    ¬ Nonempty (HSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)) := by
  simpa only [Sph, TopCat.coe_of] using not_hSpace_sphere_even_aux n hn heven hdim

/-- **The even case of Adams' theorem** (unconditional): for even `n ≥ 2`, the sphere
`Sⁿ` is not an H-space. -/
theorem not_hSpace_sphere_even' (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    ¬ Nonempty (HSpace (↥(Sph n))) :=
  not_hSpace_sphere_even_aux n hn heven (Work.Sphere.H_dim_sph_prod n hn)

/-- **The even case of Adams' theorem** (unconditional, target form). -/
theorem not_hSpace_sphere_even_uncond (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    ¬ Nonempty (HSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)) :=
  not_hSpace_sphere_even n hn heven (Work.Sphere.H_dim_sph_prod n hn)

end

end Submission.Sphere
