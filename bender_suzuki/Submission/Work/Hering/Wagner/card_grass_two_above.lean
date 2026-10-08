import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Hering.Wagner

open scoped LinearAlgebra.Projectivization

/-- Rank–nullity for the quotient map `V → V ⧸ W`: if `W ≤ T` then
`finrank (T.map W.mkQ) + finrank W = finrank T`. -/
private lemma finrank_map_mkQ {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (W T : Submodule (ZMod 2) V) (hWT : W ≤ T) :
    Module.finrank (ZMod 2) (T.map W.mkQ) + Module.finrank (ZMod 2) W
      = Module.finrank (ZMod 2) T := by
  have hfin := LinearMap.finrank_range_add_finrank_ker ((W.mkQ).domRestrict T)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hfin
  rw [← hfin]; congr 1
  rw [← Submodule.finrank_map_subtype_eq T (Submodule.comap T.subtype W.mkQ.ker), Submodule.ker_mkQ,
      Submodule.map_comap_subtype, inf_eq_right.mpr hWT]

/-- The correspondence theorem for submodules of the quotient by `W`: the `1`-dimensional
subspaces of `V ⧸ W` correspond to the `2`-dimensional subspaces of `V` containing `W`
(over `ZMod 2`, where `finrank W = 1`). -/
private def equiv_oneDim_quotient {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (W : Submodule (ZMod 2) V) (hWfin : Module.finrank (ZMod 2) W = 1) :
    ({P : Submodule (ZMod 2) (V ⧸ W) // Module.finrank (ZMod 2) P = 1} ≃
        {Y : Submodule (ZMod 2) V // W ≤ Y ∧ Module.finrank (ZMod 2) Y = 2}) :=
  { toFun := fun P => ⟨Submodule.comap W.mkQ P.1, Submodule.le_comap_mkQ W P.1, by
      have h := finrank_map_mkQ W (Submodule.comap W.mkQ P.1) (Submodule.le_comap_mkQ W P.1)
      rw [Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)] at h
      omega⟩
    invFun := fun Y => ⟨Submodule.map W.mkQ Y.1, by
      have h := finrank_map_mkQ W Y.1 Y.2.1; omega⟩
    left_inv := fun P => by
      apply Subtype.ext
      show Submodule.map W.mkQ (Submodule.comap W.mkQ P.1) = P.1
      exact Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)
    right_inv := fun Y => by
      apply Subtype.ext
      show Submodule.comap W.mkQ (Submodule.map W.mkQ Y.1) = Y.1
      rw [Submodule.comap_map_mkQ, sup_eq_right.mpr Y.2.1] }

theorem card_grass_two_above {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (a : V) (ha : a ≠ 0) :
    Nat.card {Y : Submodule (ZMod 2) V //
        Submodule.span (ZMod 2) {a} ≤ Y ∧ Module.finrank (ZMod 2) Y = 2}
      = 2 ^ (Module.finrank (ZMod 2) V - 1) - 1 := by
  classical
  set W : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {a} with hWdef
  haveI : Finite (V ⧸ W) := Finite.of_surjective W.mkQ W.mkQ_surjective
  have hWfin : Module.finrank (ZMod 2) W = 1 := by
    rw [hWdef]; simpa using finrank_span_singleton ha
  have hQfin : Module.finrank (ZMod 2) (V ⧸ W) = Module.finrank (ZMod 2) V - 1 := by
    have h := Submodule.finrank_quotient_add_finrank W
    rw [hWfin] at h; omega
  have hQcard : Nat.card (V ⧸ W) = 2 ^ (Module.finrank (ZMod 2) V - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hQfin]
  have hProj : Nat.card (ℙ (ZMod 2) (V ⧸ W)) = Nat.card (V ⧸ W) - 1 := by
    have h := Projectivization.card' (ZMod 2) (V ⧸ W)
    rw [Nat.card_zmod] at h; simp at h; omega
  calc Nat.card {Y : Submodule (ZMod 2) V // W ≤ Y ∧ Module.finrank (ZMod 2) Y = 2}
      = Nat.card {P : Submodule (ZMod 2) (V ⧸ W) // Module.finrank (ZMod 2) P = 1} :=
        Nat.card_congr (equiv_oneDim_quotient W hWfin).symm
    _ = Nat.card (ℙ (ZMod 2) (V ⧸ W)) :=
        Nat.card_congr (Projectivization.equivSubmodule (K := ZMod 2) (V := V ⧸ W)).symm
    _ = Nat.card (V ⧸ W) - 1 := hProj
    _ = 2 ^ (Module.finrank (ZMod 2) V - 1) - 1 := by rw [hQcard]

end Work.Hering.Wagner
