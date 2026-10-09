import Mathlib
import Submission.Work.Shrinking.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open TensorProduct

namespace Work.SSGRoute.PTCore

theorem tensorProduct_congr_equivariant
    (p : ℕ) {Γ M M' N N' : Type} [Group Γ]
    [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction Γ M] [SMulCommClass Γ (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N]
    [AddCommGroup M'] [Module (ZMod p) M'] [DistribMulAction Γ M'] [SMulCommClass Γ (ZMod p) M']
    [AddCommGroup N'] [Module (ZMod p) N'] [DistribMulAction Γ N'] [SMulCommClass Γ (ZMod p) N']
    (f : M ≃ₗ[ZMod p] M') (g : N ≃ₗ[ZMod p] N')
    (hf : ∀ (γ : Γ) (m : M), f (γ • m) = γ • f m)
    (hg : ∀ (γ : Γ) (n : N), g (γ • n) = γ • g n)
    (γ : Γ) (x : TensorProduct (ZMod p) M N) :
    TensorProduct.congr f g (γ • x) = γ • TensorProduct.congr f g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [hf, hg]
  | add x y hx hy => simp [map_add, smul_add, hx, hy]

end Work.SSGRoute.PTCore
