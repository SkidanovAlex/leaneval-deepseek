import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Submodule

open Module

noncomputable section

/-- If two finite-dimensional vector spaces over the same field have equal dimension,
then for every `ℓ` they have equally many submodules of dimension `ℓ`.

Proof: equal dimension gives a `K`-linear equivalence `V ≃ₗ[K] V'`.  This linear
equivalence restricts to a bijection between the submodules of `V` and those of
`V'` (via `Submodule.orderIsoMapComap`), and it preserves dimensions, since
`e.submoduleMap W : W ≃ₗ[K] W.map e` is a linear equivalence between a submodule
and its image. -/
theorem card_submodule_finrank_eq_of_finrank_eq {K V : Type*} [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [Finite V] [Module.Finite K V]
    {V' : Type*} [AddCommGroup V'] [Module K V'] [Finite V'] [Module.Finite K V']
    (h : Module.finrank K V = Module.finrank K V') {ℓ : ℕ} :
    Nat.card {W : Submodule K V // Module.finrank K W = ℓ} =
      Nat.card {W : Submodule K V' // Module.finrank K W = ℓ} := by
  let e : V ≃ₗ[K] V' := LinearEquiv.ofFinrankEq V V' h
  let F : {W : Submodule K V // Module.finrank K W = ℓ} ≃
      {W : Submodule K V' // Module.finrank K W = ℓ} := by
    refine Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv ?_
    intro W
    have hfin : Module.finrank K W = Module.finrank K (W.map (e : V →ₗ[K] V')) := by
      exact LinearEquiv.finrank_eq (e.submoduleMap W)
    have hmap : (Submodule.orderIsoMapComap e).toEquiv W = W.map (e : V →ₗ[K] V') := by
      rfl
    rw [hmap, hfin]
  exact Nat.card_congr F

end

end Commons.LinearAlgebra.Submodule