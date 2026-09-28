import Mathlib
import Submission.Work.RatHurewicz.LensSpace.Basic

namespace Work.EMFG

open Work.RatHurewicz in
theorem lensIsometry (n N : ℕ) [NeZero n] (g : Multiplicative (ZMod n))
    (x y : Work.RatHurewicz.lensTotal N) : dist (g • x) (g • y) = dist x y := by
  rw [Subtype.dist_eq, Subtype.dist_eq]
  show dist (lensAct n N g x.1) (lensAct n N g y.1) = dist x.1 y.1
  rw [lensAct, lensAct, dist_eq_norm, dist_eq_norm]
  rw [← map_sub, (cIso N).norm_map]
  rw [← smul_sub, norm_smul, phi_norm, one_mul]
  rw [← map_sub, (cIso N).symm.norm_map]

end Work.EMFG
