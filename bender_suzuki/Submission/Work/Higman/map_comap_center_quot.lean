import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

theorem map_comap_center_quot {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (φ : MulAut G) (hφ : N.map (φ : MulAut G).toMonoidHom = N) :
    ((Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N)).map (φ : MulAut G).toMonoidHom
      = (Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N) := by
  classical
  -- `Z` is the preimage in `G` of the center of `G ⧸ N`.
  set Z : Subgroup G := (Subgroup.center (G ⧸ N)).comap (QuotientGroup.mk' N) with hZ
  -- `φ` preserves `N`, so it induces an automorphism `ψ` of the quotient.
  set ψ : G ⧸ N ≃* G ⧸ N := QuotientGroup.congr N N φ hφ with hψ
  -- `ψ` and its inverse map the center onto the center (the center is characteristic).
  have hmap : Subgroup.map (ψ : G ⧸ N →* G ⧸ N) (Subgroup.center (G ⧸ N))
      = Subgroup.center (G ⧸ N) := Subgroup.map_center_eq ψ
  have hmap_symm : Subgroup.map (ψ.symm : G ⧸ N →* G ⧸ N) (Subgroup.center (G ⧸ N))
      = Subgroup.center (G ⧸ N) := Subgroup.map_center_eq ψ.symm
  -- Consequently `ψ` preserves the center: `ψ x` is central iff `x` is.
  have key : ∀ x : G ⧸ N, ψ x ∈ Subgroup.center (G ⧸ N) ↔ x ∈ Subgroup.center (G ⧸ N) := by
    intro x
    constructor
    · intro hx
      have h1 : (ψ.symm : G ⧸ N →* G ⧸ N) (ψ x) ∈
          Subgroup.map (ψ.symm : G ⧸ N →* G ⧸ N) (Subgroup.center (G ⧸ N)) :=
        Subgroup.mem_map.mpr ⟨ψ x, hx, rfl⟩
      rw [hmap_symm] at h1
      simpa using h1
    · intro hx
      have h1 : (ψ : G ⧸ N →* G ⧸ N) x ∈
          Subgroup.map (ψ : G ⧸ N →* G ⧸ N) (Subgroup.center (G ⧸ N)) :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rwa [hmap] at h1
  -- On quotient classes `ψ` acts by `mk' N x ↦ mk' N (φ x)`.
  have hψmk : ∀ x : G, ψ (QuotientGroup.mk' N x) = QuotientGroup.mk' N (φ x) :=
    fun x => QuotientGroup.congr_mk' N N φ hφ x
  -- Hence `Z` is `φ`-invariant, elementwise.
  have hiff : ∀ a : G, a ∈ Z ↔ φ a ∈ Z := by
    intro a
    have hmem : ∀ b : G, b ∈ Z ↔ QuotientGroup.mk' N b ∈ Subgroup.center (G ⧸ N) := by
      intro b; rw [hZ]; exact Subgroup.mem_comap
    rw [hmem a, hmem (φ a), ← hψmk a]
    exact (key (QuotientGroup.mk' N a)).symm
  -- Convert the elementwise invariance into the subgroup equality.
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro a ha
    exact (hiff a).mp ha
  · intro y hy
    rw [Subgroup.mem_map]
    refine ⟨φ.symm y, ?_, ?_⟩
    · exact (hiff (φ.symm y)).mpr (by simpa using hy)
    · simp

end Work.Higman
