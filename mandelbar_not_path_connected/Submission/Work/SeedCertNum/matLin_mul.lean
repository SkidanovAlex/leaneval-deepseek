import Mathlib
import Submission.Work.SeedCertNum.Mat3

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

theorem matLin_mul (a b : Fin 3 → Fin 3 → ℝ) :
    (Work.SeedCert.matLin a).comp (Work.SeedCert.matLin b) =
      Work.SeedCert.matLin (Work.SeedCert.matMul a b) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Work.SeedCert.eq_of_proj3
  intro i
  rw [ContinuousLinearMap.comp_apply, Work.SeedCert.matLin_apply]
  simp only [Work.SeedCert.matLin_apply, Work.SeedCert.matMul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

end Work.SeedCertNum
