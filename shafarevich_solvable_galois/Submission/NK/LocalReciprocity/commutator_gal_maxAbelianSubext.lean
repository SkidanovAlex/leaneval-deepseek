import Mathlib.FieldTheory.Galois.Basic
import Submission.NK.LocalReciprocity.Reciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocity

universe u v

open scoped commutatorElement

-- `haveI` is genuinely used as a typeclass instance below (it supplies `IsGalois` for the
-- maximal abelian subextension to `AlgEquiv.restrictNormalHom_surjective`); the style linter,
-- which cannot see that, asks for `have`.
set_option linter.style.haveILetI false

/-- **The Galois group of the maximal abelian subextension is abelian.**
`NK.LocalReciprocity.maxAbelianSubext F F'` is the fixed field of the commutator subgroup of
`Gal(F'/F)`, so `Gal(F^{ab}/F)` is a quotient of `Gal(F'/F)ᵃᵇ` and hence abelian.

Route: `IsGalois F (maxAbelianSubext F F')` (use `unfold maxAbelianSubext` and Mathlib's
`IsGalois.of_fixedField_normal_subgroup`, since `commutator _` is normal), hence
`Normal F (maxAbelianSubext F F')` via `IsGalois.to_normal`; then `AlgEquiv.restrictNormalHom` is
surjective (`AlgEquiv.restrictNormalHom_surjective`), its kernel is the fixing subgroup
(`IntermediateField.restrictNormalHom_ker`), and `commutator Gal(F'/F) ≤ fixingSubgroup _` because
the fixed field of a subgroup is contained in the field fixed by it
(`IntermediateField.le_iff_le ... |>.mp le_rfl`).  Then
`commutator (Gal(F^{ab}/F)) = (commutator Gal(F'/F)).map (restrictNormalHom) = ⊥`
using `Subgroup.map_commutator` and `Subgroup.map_top_of_surjective`. -/
theorem commutator_gal_maxAbelianSubext {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] :
    commutator
        ((NK.LocalReciprocity.maxAbelianSubext F F') ≃ₐ[F]
          (NK.LocalReciprocity.maxAbelianSubext F F')) = ⊥ := by
  -- it suffices to show that the commutator of any two elements of `Gal(F^{ab}/F)` is trivial
  rw [commutator_eq_bot_iff]
  refine ⟨⟨fun x y => ?_⟩⟩
  -- the maximal abelian subextension is Galois over `F`: it is the fixed field of the
  -- (normal) subgroup `commutator (Gal(F'/F))`
  haveI : IsGalois F (maxAbelianSubext F F') :=
    IsGalois.of_fixedField_normal_subgroup (commutator (F' ≃ₐ[F] F'))
  -- the restriction map `Gal(F'/F) → Gal(F^{ab}/F)` is surjective
  set φ := AlgEquiv.restrictNormalHom (F := F) (K₁ := F') (maxAbelianSubext F F') with hφ
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F)
    (K₁ := maxAbelianSubext F F') (E := F') x
  obtain ⟨h, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F)
    (K₁ := maxAbelianSubext F F') (E := F') y
  -- `commutator (Gal(F'/F))` fixes `maxAbelianSubext F F'`, by definition of the latter
  have hfix : commutator (F' ≃ₐ[F] F') ≤ (maxAbelianSubext F F').fixingSubgroup :=
    (IntermediateField.le_iff_le _ _).mp le_rfl
  have hmem : ⁅g, h⁆ ∈ (maxAbelianSubext F F').fixingSubgroup :=
    hfix (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))
  -- so the commutator `⁅g, h⁆` lies in the kernel of the restriction map
  have hker : φ ⁅g, h⁆ = 1 := by
    rw [← MonoidHom.mem_ker, hφ, IntermediateField.restrictNormalHom_ker]
    exact hmem
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at hker
  -- i.e. `φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ = 1`, so that `φ g` and `φ h` commute
  calc φ g * φ h = φ g * φ h * (φ g)⁻¹ * (φ h)⁻¹ * (φ h * φ g) := by group
    _ = φ h * φ g := by rw [hker, one_mul]

end NK.LocalReciprocity
