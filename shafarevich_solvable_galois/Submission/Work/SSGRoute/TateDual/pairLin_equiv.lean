import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.ZMod.Defs
import Submission.Work.SSGRoute.TateDual.Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TateDual

open scoped BigOperators
open Work.Tate

/-- `pairLin` is `G`-equivariant: the pairing `(f, g) ↦ ∑ x, (g x) (f x)` commutes with the
coinduced `G`-action on `f : G → M` and the dual `G`-action on the target
`Dual(coindUp G (M^∨))`. -/
theorem pairLin_equiv (p : ℕ) (G : Type) [Group G] [Fintype G]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] (γ : G) (f : G → M) :
    Work.SSGRoute.TateDual.pairLin p G M (γ • f)
      = γ • Work.SSGRoute.TateDual.pairLin p G M f := by
  ext g
  rw [Work.SSGRoute.TateDual.pairLin_apply, Work.SSGRoute.DualMod.dualSMul_apply,
      Work.SSGRoute.TateDual.pairLin_apply]
  simp only [Work.Tate.coe_smul_coindUp, Work.Tate.coind_smul_eq]
  exact Fintype.sum_equiv (Equiv.mulRight γ)
    (fun x => ((g : G → Work.SSGRoute.DualMod p M) x) (f (x * γ)))
    (fun y => ((g : G → Work.SSGRoute.DualMod p M) (y * γ⁻¹)) (f y))
    (fun x => by rw [Equiv.coe_mulRight]; simp only []; rw [mul_assoc, mul_inv_cancel, mul_one])

end Work.SSGRoute.TateDual
