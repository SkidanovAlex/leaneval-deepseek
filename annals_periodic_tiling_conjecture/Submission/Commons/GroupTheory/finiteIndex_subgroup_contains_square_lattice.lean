import Mathlib.GroupTheory.SpecificGroups.Cyclic

open scoped Pointwise

namespace Commons.GroupTheory

theorem finiteIndex_subgroup_contains_square_lattice
    {G₀ : Type*} [AddCommGroup G₀] [Finite G₀]
    (H : AddSubgroup (ℤ × ℤ × G₀)) (hH : H.FiniteIndex) :
    ∃ n : ℕ, 0 < n ∧ ((n : ℤ), 0, 0) ∈ H ∧ (0, (n : ℤ), 0) ∈ H := by
  let e₁ : ℤ × ℤ × G₀ := (1, 0, 0)
  let e₂ : ℤ × ℤ × G₀ := (0, 1, 0)
  have hcardpos : 0 < Nat.card ((ℤ × ℤ × G₀) ⧸ H) := by
    rw [← AddSubgroup.index_eq_card]
    exact Nat.pos_of_ne_zero hH.index_ne_zero
  have hfin : Finite ((ℤ × ℤ × G₀) ⧸ H) := (Nat.card_pos_iff.mp hcardpos).2
  have hnon : Nonempty ((ℤ × ℤ × G₀) ⧸ H) := (Nat.card_pos_iff.mp hcardpos).1
  let q₁ : (ℤ × ℤ × G₀) ⧸ H := QuotientAddGroup.mk' H e₁
  let q₂ : (ℤ × ℤ × G₀) ⧸ H := QuotientAddGroup.mk' H e₂
  have hq₁_pos : 0 < addOrderOf q₁ := by
    apply addOrderOf_pos
  have hq₂_pos : 0 < addOrderOf q₂ := by
    apply addOrderOf_pos
  have hq₁_zero : addOrderOf q₁ • q₁ = 0 := addOrderOf_nsmul_eq_zero q₁
  have hq₂_zero : addOrderOf q₂ • q₂ = 0 := addOrderOf_nsmul_eq_zero q₂
  have hq₁_zero' : QuotientAddGroup.mk' H (addOrderOf q₁ • e₁) = 0 := by
    simp [q₁, map_nsmul]
  have hq₂_zero' : QuotientAddGroup.mk' H (addOrderOf q₂ • e₂) = 0 := by
    simp [q₂, map_nsmul]
  have he₁mem : addOrderOf q₁ • e₁ ∈ H := by
    have h : QuotientAddGroup.mk (addOrderOf q₁ • e₁) = (0 : (ℤ × ℤ × G₀) ⧸ H) := by
      simpa [QuotientAddGroup.mk'_apply] using hq₁_zero'
    exact (QuotientAddGroup.eq_zero_iff _).mp h
  have he₂mem : addOrderOf q₂ • e₂ ∈ H := by
    have h : QuotientAddGroup.mk (addOrderOf q₂ • e₂) = (0 : (ℤ × ℤ × G₀) ⧸ H) := by
      simpa [QuotientAddGroup.mk'_apply] using hq₂_zero'
    exact (QuotientAddGroup.eq_zero_iff _).mp h
  let n : ℕ := addOrderOf q₁ * addOrderOf q₂
  have hn_pos : 0 < n := by
    dsimp [n]
    exact Nat.mul_pos hq₁_pos hq₂_pos
  refine ⟨n, hn_pos, ?_, ?_⟩
  · have hmem : n • e₁ ∈ H := by
      dsimp [n]
      rw [mul_nsmul]
      exact AddSubgroup.nsmul_mem H he₁mem (addOrderOf q₂)
    simpa [e₁, nsmul_one] using hmem
  · have hmem : n • e₂ ∈ H := by
      dsimp [n]
      rw [mul_nsmul']
      exact AddSubgroup.nsmul_mem H he₂mem (addOrderOf q₁)
    simpa [e₂, nsmul_one] using hmem

end Commons.GroupTheory