import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.PicardGroup
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq

namespace Commons.LinearAlgebra.Submodule

set_option linter.style.haveILetI false

open Module

/-- The dual annihilator and the dual coannihilator are mutually inverse bijections
between the submodules of a finite-dimensional vector space `V` and those of its dual.

This is the engine behind the Grassmann duality statement
`card_submodule_finrank_dual_zmod_two_of_le`. -/
theorem dualCoannihilator_bijective_of_finiteDimensional {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    Function.Bijective
      (Submodule.dualCoannihilator :
        Submodule K (Module.Dual K V) → Submodule K V) := by
  have hleft : ∀ W : Submodule K V,
      Submodule.dualCoannihilator (Submodule.dualAnnihilator W) = W :=
    fun W => Subspace.dualAnnihilator_dualCoannihilator_eq
  have hright : ∀ Φ : Submodule K (Module.Dual K V),
      Submodule.dualAnnihilator (Submodule.dualCoannihilator Φ) = Φ := by
    intro Φ
    exact (Submodule.eq_of_le_of_finrank_eq
      (Submodule.le_dualCoannihilator_dualAnnihilator Φ) (by
        have e1 := Subspace.finrank_add_finrank_dualCoannihilator_eq Φ
        have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq
          (Submodule.dualCoannihilator Φ)
        omega)).symm
  refine ⟨fun a b h => ?_, fun W => ⟨Submodule.dualAnnihilator W, hleft W⟩⟩
  have := congrArg Submodule.dualAnnihilator h
  rw [hright a, hright b] at this
  exact this

/-- **Grassmann duality over `𝔽₂`** (weak form): for `m ≤ finrank V`, the number of
`m`-dimensional subspaces of a finite `𝔽₂`-vector space `V` equals the number of
`(finrank V - m)`-dimensional subspaces.

Proof: `Subspace.card_submodule_finrank_eq_of_finrank_eq` transports the count to the
dual space `Module.Dual (ZMod 2) V` (which has the same dimension), and the annihilator
correspondence `Submodule.dualCoannihilator` identifies the `m`-dimensional submodules of
the dual with the `(finrank V - m)`-dimensional submodules of `V`, since
`finrank W + finrank W.dualCoannihilator = finrank V`. -/
theorem card_submodule_finrank_dual_zmod_two_of_le {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (m : ℕ) (hm : m ≤ Module.finrank (ZMod 2) V) :
    Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = m} =
      Nat.card {W : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V - m} := by
  haveI hdual_fin : Finite (Module.Dual (ZMod 2) V) := by
    haveI : Finite (V → ZMod 2) := inferInstance
    exact Finite.of_injective (fun f : Module.Dual (ZMod 2) V => (f : V → ZMod 2))
      (fun a b h => by ext x; exact congr_fun h x)
  -- The dual has the same dimension as `V`.
  have hdV : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) V) = Module.finrank (ZMod 2) V :=
    Subspace.dual_finrank_eq
  -- Step 1: transport the count to the dual space.
  have h1 : Nat.card {W : Submodule (ZMod 2) V // Module.finrank (ZMod 2) W = m} =
      Nat.card {W : Submodule (ZMod 2) (Module.Dual (ZMod 2) V) //
        Module.finrank (ZMod 2) W = m} :=
    card_submodule_finrank_eq_of_finrank_eq (K := ZMod 2) (V := V)
      (V' := Module.Dual (ZMod 2) V) hdV.symm
  -- Dimension of the coannihilator.
  have hco : ∀ Φ : Submodule (ZMod 2) (Module.Dual (ZMod 2) V),
      Module.finrank (ZMod 2) (Submodule.dualCoannihilator Φ) =
        Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) Φ := by
    intro Φ
    have := Subspace.finrank_add_finrank_dualCoannihilator_eq Φ
    omega
  -- Step 2: the coannihilator gives a bijection between the `m`-dimensional submodules
  -- of the dual and the `(finrank V - m)`-dimensional submodules of `V`.
  have hbij := dualCoannihilator_bijective_of_finiteDimensional (K := ZMod 2) (V := V)
  let e : Submodule (ZMod 2) (Module.Dual (ZMod 2) V) ≃ Submodule (ZMod 2) V :=
    Equiv.ofBijective (Submodule.dualCoannihilator) hbij
  have he : ∀ Φ, e Φ = Submodule.dualCoannihilator Φ := fun Φ => rfl
  let F : {Φ : Submodule (ZMod 2) (Module.Dual (ZMod 2) V) // Module.finrank (ZMod 2) Φ = m} ≃
      {W : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V - m} :=
    Equiv.subtypeEquiv e (fun Φ => by
      rw [he Φ, hco Φ]
      constructor
      · rintro rfl; rfl
      · intro h
        have hle : Module.finrank (ZMod 2) Φ ≤ Module.finrank (ZMod 2) V := by
          have := Subspace.finrank_add_finrank_dualCoannihilator_eq Φ
          omega
        omega)
  have h2 : Nat.card {W : Submodule (ZMod 2) (Module.Dual (ZMod 2) V) //
        Module.finrank (ZMod 2) W = m} =
      Nat.card {W : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V - m} :=
    Nat.card_congr F
  exact h1.trans h2

end Commons.LinearAlgebra.Submodule