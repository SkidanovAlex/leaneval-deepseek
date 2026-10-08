import Mathlib

/-!
# A Klein four-subgroup of `DihedralGroup 4`

`DihedralGroup 4` is the dihedral group of order `8`, with elements `r i`, `sr i` (`i : ZMod 4`).
The four elements `1`, `r 2`, `sr 0`, `sr 2` form a subgroup on which every element is an
involution; equivalently, this is the non-rotation maximal subgroup
`⟨r 2, sr 0⟩ = ⟨r^2, s⟩ ≅ C₂ × C₂`.

This file records the existence of such a subgroup, as needed for the Gorenstein–Walter
development (where `⟨r^{2^{k-1}}, s⟩` is the distinguished elementary abelian subgroup of a
dihedral 2-group).
-/

namespace Work.CORE3.MData

open DihedralGroup

/-- The underlying `Finset` of the Klein four-subgroup `{1, r 2, sr 0, sr 2}` of `DihedralGroup 4`. -/
def dihedralFourKleinSet : Finset (DihedralGroup 4) :=
  {1, r (2 : ZMod 4), sr (0 : ZMod 4), sr (2 : ZMod 4)}

/-- The Klein four-subgroup `{1, r 2, sr 0, sr 2}` of `DihedralGroup 4` (of order `8`). -/
def dihedralFourKlein : Subgroup (DihedralGroup 4) where
  carrier := (dihedralFourKleinSet : Set (DihedralGroup 4))
  one_mem' := by decide
  mul_mem' := by
    rintro x y hx hy
    simp only [dihedralFourKleinSet, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> decide
  inv_mem' := by
    rintro x hx
    simp only [dihedralFourKleinSet, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> decide

lemma mem_dihedralFourKlein (x : DihedralGroup 4) :
    x ∈ dihedralFourKlein ↔
      x = 1 ∨ x = r (2 : ZMod 4) ∨ x = sr (0 : ZMod 4) ∨ x = sr (2 : ZMod 4) := by
  show x ∈ (dihedralFourKleinSet : Set (DihedralGroup 4)) ↔ _
  simp only [dihedralFourKleinSet, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]

/-- `dihedralFourKlein` has order `4`. -/
lemma card_dihedralFourKlein : Nat.card dihedralFourKlein = 4 := by
  rw [show Nat.card ↥dihedralFourKlein =
        (dihedralFourKlein : Set (DihedralGroup 4)).ncard from Nat.card_coe_set_eq _]
  show (dihedralFourKleinSet : Set (DihedralGroup 4)).ncard = 4
  rw [Set.ncard_coe_finset]
  decide

/-- Every element of `dihedralFourKlein` is an involution. -/
lemma mul_self_of_mem_dihedralFourKlein {v : DihedralGroup 4} (hv : v ∈ dihedralFourKlein) :
    v * v = 1 := by
  rw [mem_dihedralFourKlein] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> decide

theorem FourGroupDihedralFour :
    ∃ V : Subgroup (DihedralGroup 4), Nat.card V = 4 ∧ ∀ v ∈ V, v * v = 1 :=
  ⟨dihedralFourKlein, card_dihedralFourKlein,
    fun _ hv => mul_self_of_mem_dihedralFourKlein hv⟩

end Work.CORE3.MData
