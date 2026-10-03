import Mathlib
import Submission.Work.ORLyndon.DiagTensor

open TensorProduct

-- Mathlib's "left" `K[G]`-action on `N ⊗[K] M` (`a • (n ⊗ m) = (a • n) ⊗ m`) is *not* the
-- diagonal action we use below; remove those instances so that instance search picks the
-- diagonal structure `Work.ORLyndon.diagModule` defined in `DiagTensor.lean`.
-- (As in `DiagTensor.lean` this removal is local to the current file.)
attribute [-instance] TensorProduct.leftModule TensorProduct.leftDistribMulAction
  TensorProduct.leftHasSMul

namespace Work.ORLyndon

universe u v

/-- Tensoring the free module `ι →₀ N` (with its pointwise `K[G]`-action) with `M` over `K`
commutes with the direct sum: `(ι →₀ N) ⊗[K] M ≃ₗ[K[G]] ι →₀ (N ⊗[K] M)`, where both sides
carry the diagonal `K[G]`-action. -/
theorem diagTensor_finsupp {K : Type v} [Field K] {G : Type u} [Group G]
    {M : Type (max u v)} [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
    [IsScalarTower K (MonoidAlgebra K G) M]
    {N : Type (max u v)} [AddCommGroup N] [Module K N] [Module (MonoidAlgebra K G) N]
    [IsScalarTower K (MonoidAlgebra K G) N] (ι : Type (max u v)) :
    Nonempty ((TensorProduct K (ι →₀ N) M) ≃ₗ[MonoidAlgebra K G]
      (ι →₀ (TensorProduct K N M))) := by
  classical
  -- `TensorProduct.finsuppLeft` is the `K`-linear equivalence
  -- `(ι →₀ N) ⊗[K] M ≃ₗ[K] ι →₀ (N ⊗[K] M)`, `p ⊗ₜ m ↦ (i ↦ p i ⊗ₜ m)`.
  -- We only have to check that it commutes with the diagonal action of group elements.
  have key : ∀ (g : G) (t : TensorProduct K (ι →₀ N) M),
      TensorProduct.finsuppLeft K K N M ι (MonoidAlgebra.single g (1 : K) • t) =
        MonoidAlgebra.single g (1 : K) • TensorProduct.finsuppLeft K K N M ι t := by
    intro g t
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, LinearEquiv.map_zero]
    | add x y hx hy => simp only [smul_add, LinearEquiv.map_add, hx, hy]
    | tmul p m =>
        rw [diagModule_single_tmul (K := K) (N := ι →₀ N) (M := M) g p m]
        ext i
        simp only [TensorProduct.finsuppLeft_apply_tmul_apply, Finsupp.smul_apply,
          diagModule_single_tmul]
  -- Lift the `K`-linear equivalence to a `K[G]`-linear one; it is still a bijection.
  exact ⟨LinearEquiv.ofBijective
    (MonoidAlgebra.equivariantOfLinearOfComm
      ((TensorProduct.finsuppLeft K K N M ι :
        TensorProduct K (ι →₀ N) M ≃ₗ[K] ι →₀ TensorProduct K N M) :
        TensorProduct K (ι →₀ N) M →ₗ[K] ι →₀ TensorProduct K N M) key)
    (TensorProduct.finsuppLeft K K N M ι).bijective⟩

end Work.ORLyndon
