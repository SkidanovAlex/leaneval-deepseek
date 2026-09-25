import Mathlib
import Submission.NK.LocalReciprocity.Reciprocity

namespace NK.LocalReciprocity

universe u v

/-- **Maximality of the maximal abelian subextension**: every finite normal subextension
`L ≤ F'` whose Galois group over `F` is commutative lies in
`NK.LocalReciprocity.maxAbelianSubext F F'`.

Route: `rw [NK.LocalReciprocity.maxAbelianSubext]` and
`(IntermediateField.le_iff_le L (commutator (F' ≃ₐ[F] F'))).mpr`; it remains to show
`commutator Gal(F'/F) ≤ L.fixingSubgroup`, i.e. that the restriction homomorphism
`AlgEquiv.restrictNormalHom` (surjective, since `Normal F ↥L` and `Normal F F'`) kills the
commutator: `(commutator Gal(F'/F)).map (restrictNormalHom) = commutator Gal(L/F) = ⊥` by
`Subgroup.map_commutator` and `hcomm`. -/
theorem le_maxAbelianSubext_of_commutative {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] (L : IntermediateField F F') [FiniteDimensional F ↥L]
    [Normal F ↥L] (hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ) :
    L ≤ NK.LocalReciprocity.maxAbelianSubext F F' := by
  -- unfold the maximal abelian subextension: it is the fixed field of the commutator subgroup
  show L ≤ IntermediateField.fixedField (commutator (F' ≃ₐ[F] F'))
  -- it suffices that `commutator Gal(F'/F) ≤ L.fixingSubgroup`
  refine (IntermediateField.le_iff_le (commutator (F' ≃ₐ[F] F')) L).mpr ?_
  -- the restriction homomorphism `Gal(F'/F) →* Gal(L/F)`
  set φ : (F' ≃ₐ[F] F') →* (↥L ≃ₐ[F] ↥L) :=
    AlgEquiv.restrictNormalHom (F := F) (K₁ := F') L with hφ
  -- it is surjective because `L` and `F'` are normal over `F`
  have hsurj : Function.Surjective φ :=
    AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥L) (E := F')
  -- `Gal(L/F)` is commutative, so its commutator subgroup is trivial
  have habel : commutator (↥L ≃ₐ[F] ↥L) = ⊥ := by
    rw [commutator_eq_bot_iff]
    exact ⟨⟨fun x y => hcomm x y⟩⟩
  -- hence the image of `commutator Gal(F'/F)` under restriction is trivial
  have hmap : Subgroup.map φ (commutator (F' ≃ₐ[F] F')) = ⊥ := by
    rw [show commutator (F' ≃ₐ[F] F') = ⁅⊤, ⊤⁆ from rfl, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hsurj]
    exact habel
  -- so `commutator Gal(F'/F)` is contained in the kernel of the restriction map ...
  intro σ hσ
  have hker : σ ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    have h : φ σ ∈ Subgroup.map φ (commutator (F' ≃ₐ[F] F')) := ⟨σ, hσ, rfl⟩
    rw [hmap] at h
    simpa using h
  -- ... which is exactly the fixing subgroup of `L`
  rwa [hφ, IntermediateField.restrictNormalHom_ker L] at hker

end NK.LocalReciprocity
