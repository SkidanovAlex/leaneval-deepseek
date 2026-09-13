import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_dual_zmod_two_of_le

namespace Commons.LinearAlgebra.Submodule

set_option linter.style.haveILetI false

open Module

/-- **Grassmann duality** over any finite field: for `m ≤ finrank V`, the number of
`m`-dimensional subspaces of a finite `K`-vector space `V` equals the number of
`(finrank V - m)`-dimensional subspaces.

Proof: `card_submodule_finrank_eq_of_finrank_eq` transports the count to the dual space
`Module.Dual K V` (which has the same dimension), and the annihilator correspondence
`Submodule.dualCoannihilator` identifies the `m`-dimensional submodules of the dual with
the `(finrank V - m)`-dimensional submodules of `V`, since
`finrank W + finrank W.dualCoannihilator = finrank V`. -/
theorem card_submodule_finrank_eq_compl {K : Type*} [Field K] [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [Finite V] (m : ℕ) (hm : m ≤ Module.finrank K V) :
    Nat.card {W : Submodule K V // Module.finrank K W = m} =
      Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - m} := by
  haveI hdual_fin : Finite (Module.Dual K V) := by
    haveI : Finite (V → K) := inferInstance
    exact Finite.of_injective (fun f : Module.Dual K V => (f : V → K))
      (fun a b h => by ext x; exact congr_fun h x)
  -- The dual has the same dimension as `V`.
  have hdV : Module.finrank K (Module.Dual K V) = Module.finrank K V :=
    Subspace.dual_finrank_eq
  -- Step 1: transport the count to the dual space.
  have h1 : Nat.card {W : Submodule K V // Module.finrank K W = m} =
      Nat.card {W : Submodule K (Module.Dual K V) // Module.finrank K W = m} :=
    card_submodule_finrank_eq_of_finrank_eq (K := K) (V := V)
      (V' := Module.Dual K V) hdV.symm
  -- Dimension of the coannihilator.
  have hco : ∀ Φ : Submodule K (Module.Dual K V),
      Module.finrank K (Submodule.dualCoannihilator Φ) =
        Module.finrank K V - Module.finrank K Φ := by
    intro Φ
    have := Subspace.finrank_add_finrank_dualCoannihilator_eq Φ
    omega
  -- Step 2: the coannihilator gives a bijection between the `m`-dimensional submodules
  -- of the dual and the `(finrank V - m)`-dimensional submodules of `V`.
  have hbij := dualCoannihilator_bijective_of_finiteDimensional (K := K) (V := V)
  let e : Submodule K (Module.Dual K V) ≃ Submodule K V :=
    Equiv.ofBijective (Submodule.dualCoannihilator) hbij
  have he : ∀ Φ, e Φ = Submodule.dualCoannihilator Φ := fun Φ => rfl
  let F : {Φ : Submodule K (Module.Dual K V) // Module.finrank K Φ = m} ≃
      {W : Submodule K V // Module.finrank K W = Module.finrank K V - m} :=
    Equiv.subtypeEquiv e (fun Φ => by
      rw [he Φ, hco Φ]
      constructor
      · rintro rfl; rfl
      · intro h
        have hle : Module.finrank K Φ ≤ Module.finrank K V := by
          have := Subspace.finrank_add_finrank_dualCoannihilator_eq Φ
          omega
        omega)
  have h2 : Nat.card {W : Submodule K (Module.Dual K V) // Module.finrank K W = m} =
      Nat.card {W : Submodule K V // Module.finrank K W = Module.finrank K V - m} :=
    Nat.card_congr F
  exact h1.trans h2

end Commons.LinearAlgebra.Submodule
