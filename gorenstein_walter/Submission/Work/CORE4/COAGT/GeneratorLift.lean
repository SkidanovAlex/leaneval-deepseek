import Mathlib

namespace Work.CORE4.COAGT

/-- If `Y Z / Z` (the image of a subgroup `Y` in `E ⧸ Z`) is cyclic, then some `y₀ ∈ Y` maps to a
generator, and every `y ∈ Y` is of the form `y₀ ^ j * z` with `j : ℤ`, `z ∈ Z`. -/
theorem GeneratorLift {E : Type*} [Group E] (Z : Subgroup E) [Z.Normal]
    (Y : Subgroup E) (h : IsCyclic (Y.map (QuotientGroup.mk' Z))) :
    ∃ y₀ ∈ Y, ∀ y ∈ Y, ∃ j : ℤ, ∃ z ∈ Z, y = y₀ ^ j * z := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_zpow_surjective (G := ↥(Y.map (QuotientGroup.mk' Z)))
  obtain ⟨y₀, hy₀Y, hy₀⟩ := Subgroup.mem_map.mp g.2
  refine ⟨y₀, hy₀Y, ?_⟩
  intro y hy
  have hmem : QuotientGroup.mk' Z y ∈ Y.map (QuotientGroup.mk' Z) :=
    Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  obtain ⟨j, hj⟩ := hg ⟨QuotientGroup.mk' Z y, hmem⟩
  refine ⟨j, y₀ ^ (-j) * y, ?_, ?_⟩
  · rw [← QuotientGroup.ker_mk' (N := Z), MonoidHom.mem_ker]
    have hval : (↑(g ^ j) : E ⧸ Z) = QuotientGroup.mk' Z y := congrArg Subtype.val hj
    rw [Subgroup.coe_zpow] at hval
    rw [map_mul, map_zpow, hy₀, zpow_neg, hval, inv_mul_cancel]
  · group

end Work.CORE4.COAGT
