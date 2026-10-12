import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseKinLoc.Momentum.momDefs
import Submission.Work.OneBodyKin.BoxHat.boxHat_scale
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Momentum

/-- The scale-free unit-cube symbol `cubFT` is the `ℓ = 1` box profile `boxHat 1`: both are the
(real, cos-only) integral of `cos⟪q,z⟫` over the unit cube `acube 1`. -/
lemma cubFT_eq_boxHat_one (q : EuclideanSpace ℝ (Fin 3)) :
    cubFT q = Work.OneBodyKin.boxHat 1 q := rfl

theorem boxHat_eq_cubFT {ℓ : ℝ} (hℓ : 0 < ℓ) (q : EuclideanSpace ℝ (Fin 3)) : Work.OneBodyKin.boxHat ℓ q = ℓ ^ 3 * Work.BoseKinLoc.Momentum.cubFT (ℓ • q) := by
  rw [Work.OneBodyKin.BoxHat.boxHat_scale hℓ q, cubFT_eq_boxHat_one]

end Work.BoseKinLoc.Momentum
