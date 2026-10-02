import Mathlib
import Submission.Work.SeedCertNum.Mat3

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

/-- A point of `E3` is the sum of its coordinates times the unit vectors `vec3 j`. -/
theorem vec_decomp (v : E3) : v = ∑ j : Fin 3, (proj3 j v) • vec3 j := by
  apply eq_of_proj3
  intro i
  rw [map_sum]
  simp only [map_smul, proj3_vec3, smul_eq_mul]
  rw [show (∑ j : Fin 3, proj3 j v * (if i = j then 1 else 0))
        = ∑ j : Fin 3, (if i = j then proj3 j v else 0) from by
      apply Finset.sum_congr rfl; intro j _; by_cases h : i = j <;> simp [h]]
  rw [Finset.sum_ite_eq]
  simp

end Work.SeedCert

namespace Work.SeedCertNum

theorem matLin_matOf (L : Work.SeedCert.E3 →L[ℝ] Work.SeedCert.E3) :
    Work.SeedCert.matLin (Work.SeedCert.matOf L) = L := by
  apply ContinuousLinearMap.ext
  intro v
  apply Work.SeedCert.eq_of_proj3
  intro i
  rw [Work.SeedCert.matLin_apply]
  conv_rhs => rw [Work.SeedCert.vec_decomp v]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Work.SeedCert.matOf]
  ring

end Work.SeedCertNum
