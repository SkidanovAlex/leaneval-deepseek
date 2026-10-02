import Mathlib
import Submission.Work.SeedCertNum.Mat3

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

/-- Contracting a row of the identity matrix: `∑_j (𝟙) i j * x j = x i`. -/
theorem matId_mul_sum (x : Fin 3 → ℝ) (i : Fin 3) :
    ∑ j, Work.SeedCert.matId i j * x j = x i := by
  simp [Work.SeedCert.matId, Finset.mem_univ]

/-- Subtracting the identity from the linear map of a matrix is the linear map of the matrix with
the identity subtracted: `matLin a - 1 = matLin (a - 𝟙)`. -/
theorem matLin_sub_id (a : Fin 3 → Fin 3 → ℝ) :
    Work.SeedCert.matLin a - ContinuousLinearMap.id ℝ Work.SeedCert.E3 =
      Work.SeedCert.matLin (Work.SeedCert.matSub a Work.SeedCert.matId) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Work.SeedCert.eq_of_proj3
  intro i
  rw [sub_apply, ContinuousLinearMap.id_apply, map_sub]
  rw [Work.SeedCert.matLin_apply, Work.SeedCert.matLin_apply]
  simp only [Work.SeedCert.matSub]
  rw [show (∑ j, (a i j - Work.SeedCert.matId i j) * (Work.SeedCert.proj3 j) v)
       = ∑ j, (a i j * (Work.SeedCert.proj3 j) v
                - Work.SeedCert.matId i j * (Work.SeedCert.proj3 j) v) from
      Finset.sum_congr rfl (fun j _ => by rw [sub_mul])]
  rw [Finset.sum_sub_distrib, matId_mul_sum]

end Work.SeedCertNum
