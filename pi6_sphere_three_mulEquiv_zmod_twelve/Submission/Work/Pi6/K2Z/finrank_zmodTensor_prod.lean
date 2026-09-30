import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.K2Z

/-- Tensor product with `ZMod p` commutes with (binary) products, so the `ZMod p`-dimension of
`ZMod p ⊗[ℤ] (M × N)` is the sum of the dimensions of `ZMod p ⊗[ℤ] M` and `ZMod p ⊗[ℤ] N`,
for `M, N` finite `ℤ`-modules and `p` prime. -/
theorem finrank_zmodTensor_prod (p : ℕ) (hp : p.Prime) (M N : Type*) [AddCommGroup M] [Module ℤ M]
    [Module.Finite ℤ M] [AddCommGroup N] [Module ℤ N] [Module.Finite ℤ N] :
    Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (M × N))
      = Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) M)
        + Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) N) := by
  have : Fact p.Prime := ⟨hp⟩
  -- The `ℤ`-module structure on `M × N` used to form the tensor product in the statement is the
  -- canonical one coming from the `AddCommGroup` structure; rewrite it to the product instance so
  -- that `TensorProduct.prodRight` applies syntactically.
  have hinst : (Prod.instModule : Module ℤ (M × N)) = AddCommGroup.toIntModule (M × N) :=
    Subsingleton.elim _ _
  rw [← hinst]
  exact (LinearEquiv.finrank_eq (TensorProduct.prodRight ℤ (ZMod p) (ZMod p) M N)).trans
    Module.finrank_prod

end Work.Pi6.K2Z
