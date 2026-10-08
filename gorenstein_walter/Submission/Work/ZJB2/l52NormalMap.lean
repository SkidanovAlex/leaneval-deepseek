import Mathlib
import Submission.Work.ZJB2.Defs

namespace Work.ZJB2

/-- `K` is the subgroup of `D` consisting of the elements whose order is coprime to `p`;
this property is preserved by every automorphism of `D`, so `K` is characteristic in `D`. -/
theorem l52NormalMap_characteristic {Q : Type} [Group Q] {D : Subgroup Q} {p : ℕ}
    {K : Subgroup ↥D} (hK : ∀ x : ↥D, x ∈ K ↔ Nat.Coprime (orderOf x) p) :
    K.Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hK] at hy ⊢
    rw [orderOf_injective φ.toMonoidHom φ.injective y]
    exact hy
  · intro hx
    refine ⟨φ.symm x, ?_, φ.apply_symm_apply x⟩
    rw [hK] at hx ⊢
    rw [MulEquiv.orderOf_eq φ.symm x]
    exact hx

theorem l52NormalMap {Q : Type} [Group Q] {D : Subgroup Q} (hD : D.Normal) {p : ℕ}
    {K : Subgroup ↥D} (hK : ∀ x : ↥D, x ∈ K ↔ Nat.Coprime (orderOf x) p) :
    (K.map D.subtype).Normal := by
  have : D.Normal := hD
  have : K.Characteristic := l52NormalMap_characteristic hK
  exact ConjAct.normal_of_characteristic_of_normal

end Work.ZJB2
