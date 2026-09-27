/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: hSpace_sphere_iff team

# The cohomology of a product of two spheres

`H_prod_sph` computes the rational cohomology of `S^p × S^q` for `0 < p < q`: it is `ℚ` in
degrees `p` and `q`, and it vanishes in every other positive degree except `p + q`.

The proof is the induction `Work.Sphere.prod_sph_main_of_bases`
(`Submission/Work/Sphere/ProdMain.lean`) on `p + q`, driven by the two degree shifts
`prod_fst_shift`/`prod_snd_shift` (`Submission/Work/Sphere/ProdRec.lean`), together with the
values of the cohomology of the spheres (`Submission/Work/Sphere/Values.lean`) and the five base
cases that the shifts cannot reach:
`Work.Sphere.H1_prod_sph_high`, `Work.Sphere.H1_prod_sph_circle`, `Work.Sphere.Htop_prod_sph`,
`Work.Sphere.H_prod_sph_zero` and `Work.Sphere.Hdiag_prod_sph_zero`.  The result is transported
from the singular complex of the honest product space `S^p × S^q` to the tensor product
`singSph p ⊗ singSph q` of the two singular complexes by `H_tensor_homeo`.
-/
import Mathlib
import Submission.Work.Sphere.ProdSetup
import Submission.Work.Sphere.ProdRec
import Submission.Work.Sphere.ProdMain
import Submission.Work.Sphere.Values
import Submission.Work.Sphere.H1_prod_sph_high
import Submission.Work.Sphere.H1_prod_sph_circle
import Submission.Work.Sphere.Htop_prod_sph
import Submission.Work.Sphere.H_prod_sph_zero
import Submission.Work.Sphere.Hdiag_prod_sph_zero

open CategoryTheory Simplicial Opposite

namespace Work.Sphere

open Submission.Cohomology Submission.Sphere

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem H_prod_sph (p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (hsphere : ∀ k : ℕ, 0 < k → k < q → Subsingleton (Submission.Cohomology.H (Submission.Sphere.singSph q) ℚ k)) :
    Nonempty (Submission.Cohomology.H
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (Submission.Sphere.singSph p)
          (Submission.Sphere.singSph q)) ℚ p ≃ₗ[ℚ] ℚ) ∧
      Nonempty (Submission.Cohomology.H
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (Submission.Sphere.singSph p)
          (Submission.Sphere.singSph q)) ℚ q ≃ₗ[ℚ] ℚ) ∧
      (∀ k : ℕ, 0 < k → k ≠ p → k ≠ q → k ≠ p + q → Subsingleton (Submission.Cohomology.H
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (Submission.Sphere.singSph p)
          (Submission.Sphere.singSph q)) ℚ k)) := by
  -- the five base cases of the induction
  have hmain := prod_sph_main_of_bases
    (fun p q hp hpq => H1_prod_sph_high p q hp hpq)
    (fun q hq => H1_prod_sph_circle q hq)
    (fun p hp => Htop_prod_sph p hp)
    (fun q j hj hjq => H_prod_sph_zero q j hj hjq)
    (fun p hp => Hdiag_prod_sph_zero p hp)
    p q (by omega) hpq
  refine ⟨?_, ?_, ?_⟩
  · exact ne_trans (H_tensor_homeo (Sph p) (Sph q) p) hmain.1
  · exact ne_trans (H_tensor_homeo (Sph p) (Sph q) q) hmain.2.1
  · intro k hk hkp hkq hkpq
    exact subs_trans (H_tensor_homeo (Sph p) (Sph q) k)
      (hmain.2.2 k hk hkp hkq hkpq)

end

end Work.Sphere
