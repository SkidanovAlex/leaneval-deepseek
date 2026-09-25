import Mathlib

namespace Work.LT

/-- The submodules `W ≤ U` of `V` of dimension `j` are in bijection with the submodules of `U`
of dimension `j`: both directions are given by transporting along the inclusion `U ↪ V`, which
preserves the dimension. -/
theorem gb_submodule_le_equiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (U : Submodule (ZMod 2) V) (j : ℕ) :
    Nat.card {W : Submodule (ZMod 2) V // W ≤ U ∧ Module.finrank (ZMod 2) W = j} =
      Nat.card {W' : Submodule (ZMod 2) U // Module.finrank (ZMod 2) W' = j} := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun W => ⟨Submodule.comap U.subtype W.1, ?_⟩
      invFun := fun W' => ⟨Submodule.map U.subtype W'.1, Submodule.map_subtype_le U W'.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [← Submodule.finrank_map_subtype_eq U (Submodule.comap U.subtype W.1),
      Submodule.map_comap_subtype, inf_of_le_right W.2.1]
    exact W.2.2
  · rw [Submodule.finrank_map_subtype_eq]
    exact W'.2
  · intro W
    exact Subtype.ext (by
      change Submodule.map U.subtype (Submodule.comap U.subtype W.1) = W.1
      rw [Submodule.map_comap_subtype, inf_of_le_right W.2.1])
  · intro W'
    exact Subtype.ext (by
      change Submodule.comap U.subtype (Submodule.map U.subtype W'.1) = W'.1
      exact (Submodule.MapSubtype.orderIso U).left_inv W'.1)

end Work.LT
