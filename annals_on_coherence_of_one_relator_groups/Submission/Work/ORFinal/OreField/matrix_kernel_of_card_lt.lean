import Mathlib

namespace Work.ORFinal.OreField

open Matrix

/-- A homogeneous linear system over a division ring with more unknowns than equations has a
nonzero solution: any `m × n` matrix `A` with `m < n` has a nontrivial kernel.

The proof passes to the opposite ring `Dᵐᵒᵖ`: the matrix-vector product `A *ᵥ ·` over `D`
corresponds, under `MulOpposite.op` and transposition, to a `Dᵐᵒᵖ`-linear map
`(Fin n → Dᵐᵒᵖ) →ₗ[Dᵐᵒᵖ] (Fin m → Dᵐᵒᵖ)`, and the rank–nullity theorem over the division
ring `Dᵐᵒᵖ` gives a nontrivial kernel. -/
theorem matrix_kernel_of_card_lt {D : Type*} [DivisionRing D] {m n : ℕ} (hmn : m < n)
    (A : Matrix (Fin m) (Fin n) D) :
    ∃ v : Fin n → D, v ≠ 0 ∧ A.mulVec v = 0 := by
  classical
  -- `B j i = op (A i j)`: the transpose of `A` with entries pushed into the opposite ring.
  let B : Matrix (Fin n) (Fin m) Dᵐᵒᵖ := (Aᵀ).map MulOpposite.op
  -- `A *ᵥ ·`, transported to the opposite ring, is `· ᵥ* B`, which is linear over `Dᵐᵒᵖ`.
  let f : (Fin n → Dᵐᵒᵖ) →ₗ[Dᵐᵒᵖ] (Fin m → Dᵐᵒᵖ) :=
    { toFun := fun u => u ᵥ* B
      map_add' := fun u w => add_vecMul B u w
      map_smul' := fun c u => smul_vecMul c u B }
  have hker : LinearMap.ker f ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact hmn
  obtain ⟨u, hu, hune⟩ := (Submodule.ne_bot_iff (LinearMap.ker f)).mp hker
  have hu0 : u ᵥ* B = 0 := hu
  refine ⟨fun j => (u j).unop, ?_, ?_⟩
  · -- a nonzero `u` has a nonzero `unop`
    intro hv
    apply hune
    funext j
    have h : (u j).unop = 0 := congrFun hv j
    simpa using congrArg MulOpposite.op h
  · -- `u ᵥ* B = 0` means `op ∘ (A *ᵥ ·) u = 0`, i.e. `A *ᵥ u.unop = 0`
    funext i
    have hsum : MulOpposite.op (∑ j : Fin n, A i j * (u j).unop)
        = ∑ j : Fin n, MulOpposite.op (A i j * (u j).unop) :=
      map_sum MulOpposite.opAddEquiv _ _
    have h1 : (u ᵥ* B) i = MulOpposite.op ((A *ᵥ fun j => (u j).unop) i) := by
      rw [Matrix.vecMul_apply_eq_sum, Matrix.mulVec_apply_eq_sum, hsum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      dsimp only [B]
      simp [Matrix.map_apply, MulOpposite.op_mul]
    have h2 : (u ᵥ* B) i = 0 := by rw [hu0]; rfl
    rw [h1] at h2
    exact (MulOpposite.op_eq_zero_iff _).mp h2

end Work.ORFinal.OreField
