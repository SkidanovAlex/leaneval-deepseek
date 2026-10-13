import Mathlib

namespace Work.DSG2

theorem privateAffineOpens (X : AlgebraicGeometry.Scheme) [AlgebraicGeometry.IsNoetherian X] :
    ∃ A : (C : Set X) → C ∈ irreducibleComponents X → X.affineOpens,
      (∀ (C : Set X) (hC : C ∈ irreducibleComponents X), (A C hC : Set X).Nonempty) ∧
        (∀ (C : Set X) (hC : C ∈ irreducibleComponents X),
          (A C hC : Set X) ⊆ (⋃₀ (irreducibleComponents X \ {C}))ᶜ) := by
  classical
  -- `X` is Noetherian, hence has finitely many irreducible components.
  have hfin : (irreducibleComponents X).Finite :=
    AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
  -- The complement of the union of the other components is open.
  have hopen : ∀ C : Set X, IsOpen ((⋃₀ (irreducibleComponents X \ {C}))ᶜ : Set X) := by
    intro C
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfin.sdiff.isClosed_biUnion (fun W hW => isClosed_of_mem_irreducibleComponents W hW.1)
  -- ... and nonempty: its closure is exactly `C`, which is nonempty.
  have hne : ∀ C (hC : C ∈ irreducibleComponents X),
      ((⋃₀ (irreducibleComponents X \ {C}))ᶜ : Set X).Nonempty := by
    intro C hC
    have hcl : closure ((⋃₀ (irreducibleComponents X \ {C}))ᶜ : Set X) = C :=
      closure_sUnion_irreducibleComponents_sdiff_singleton hfin C hC
    apply closure_nonempty_iff.mp
    rw [hcl]
    exact hC.1.1
  -- Affine opens form a basis, so each such complement contains an affine open.
  have hex : ∀ C (hC : C ∈ irreducibleComponents X),
      ∃ W : X.affineOpens,
        (W : Set X).Nonempty ∧ (W : Set X) ⊆ (⋃₀ (irreducibleComponents X \ {C}))ᶜ := by
    intro C hC
    obtain ⟨x, hxS⟩ := hne C hC
    obtain ⟨v, ⟨W, hW, rfl⟩, hxv, hvS⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxS (hopen C)
    exact ⟨⟨W, hW⟩, ⟨x, hxv⟩, hvS⟩
  exact ⟨fun C hC => (hex C hC).choose,
    fun C hC => (hex C hC).choose_spec.1,
    fun C hC => (hex C hC).choose_spec.2⟩

end Work.DSG2
