import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Surjections from a finite cyclic group onto `ZMod m` when `m ∣ |G|`

If `G` is a finite cyclic group and `m ∣ Nat.card G`, then `G` admits a
surjective homomorphism onto the (multiplicative) group `ZMod m`.

This is the elementary cyclicity statement used when one wants to push a
generator of a cyclic quotient along divisibility of the order.

The proof composes the canonical isomorphism `G ≃* Multiplicative (ZMod |G|)`
(valid for any cyclic group, see `zmodCyclicMulEquiv`) with reduction
`ZMod |G| →+* ZMod m` (`ZMod.castHom`), which is surjective by
`ZMod.castHom_surjective`.
-/

namespace NK.RankTheoryDeep

open Multiplicative

theorem exists_surjective_hom_zmod_of_cyclic {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    {m : ℕ} (hm : m ∣ Nat.card G) :
    ∃ φ : G →* Multiplicative (ZMod m), Function.Surjective φ := by
  -- Transport the generator of `G` to `ZMod (Nat.card G)` and reduce modulo `m`.
  let e : G ≃* Multiplicative (ZMod (Nat.card G)) :=
    (zmodCyclicMulEquiv (inferInstance : IsCyclic G)).symm
  let ψ : Multiplicative (ZMod (Nat.card G)) →* Multiplicative (ZMod m) :=
    AddMonoidHom.toMultiplicative ((ZMod.castHom hm (ZMod m)).toAddMonoidHom)
  refine ⟨ψ.comp e.toMonoidHom, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective hm y.toAdd
  refine ⟨e.symm (Multiplicative.ofAdd x), ?_⟩
  simp [ψ, hx]

end NK.RankTheoryDeep
