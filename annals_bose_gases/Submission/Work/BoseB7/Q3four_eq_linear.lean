import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Submission.Work.BoseB7.Estimates
import Submission.Work.BoseB7.bCommutator_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7

theorem Q3four_eq_linear {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) :
    F.Q3four E = (E.z / E.ell ^ 3) • ∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ F.PHset E,
      ((F.ccrK (s - k) (-k) - E.alpha (s - k) * E.alpha (-k) * F.ccrK k (k - s))
        * (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k))) • (F.aDag s + F.a s) := by
  -- `Q3four` is the `bCommutator` word; the squeezed commutator
  -- `[b_{s-k}, b_{-k}†]` is the scalar `(ccrK (s-k) (-k) - α_{s-k}α_{-k}ccrK k (k-s))`
  -- times the identity (`bCommutator_eq`), so the words collapse pointwise.
  rw [FockData.Q3four]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro k hk
  rw [bCommutator_eq F E s k]
  ext f
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, Module.End.one_apply, smul_smul]
  rw [mul_comm (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k))
    (F.ccrK (s - k) (-k) - E.alpha (s - k) * E.alpha (-k) * F.ccrK k (k - s))]

end Work.BoseB7
