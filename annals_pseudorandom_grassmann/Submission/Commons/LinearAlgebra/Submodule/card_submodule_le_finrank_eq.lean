import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Commons.LinearAlgebra.Submodule

open Module

noncomputable section

/-- Submodules of `V` that are contained in `W0` are in dimension-preserving bijection
with the submodules of `W0` itself: the order isomorphism
`Submodule.MapSubtype.orderIso W0 : Submodule K ↥W0 ≃o {p // p ≤ W0}` sends a submodule
`u ≤ W0` to its image `u.map W0.subtype`, and `Submodule.finrank_map_subtype_eq` shows this
image has the same `finrank`.  Consequently the number of `m`-dimensional submodules of `V`
lying inside `W0` equals the number of `m`-dimensional submodules of `W0`. -/
theorem card_submodule_le_finrank_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W0 : Submodule K V) (m : ℕ) :
    Nat.card {x : Submodule K V // x ≤ W0 ∧ Module.finrank K x = m} =
      Nat.card {u : Submodule K ↥W0 // Module.finrank K u = m} := by
  classical
  let p : Submodule K V → Prop := fun x => x ≤ W0
  let q : Submodule K V → Prop := fun x => Module.finrank K x = m
  let e := Submodule.MapSubtype.orderIso W0
  have hfun : ∀ u : Submodule K ↥W0, (e u).1 = Submodule.map W0.subtype u := fun _ => rfl
  have h : ∀ u : Submodule K ↥W0, (Module.finrank K u = m) ↔
      (fun x : {x // p x} => Module.finrank K x.1 = m) (e u) := by
    intro u
    change (Module.finrank K u = m) ↔ (Module.finrank K ((e u).1) = m)
    rw [hfun u, Submodule.finrank_map_subtype_eq]
  exact Nat.card_congr
    ((Equiv.subtypeSubtypeEquivSubtypeInter p q).symm.trans (e.subtypeEquiv h).symm)

end

end Commons.LinearAlgebra.Submodule