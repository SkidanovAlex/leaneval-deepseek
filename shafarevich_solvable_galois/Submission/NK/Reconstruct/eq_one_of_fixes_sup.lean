import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# An automorphism of a compositum fixing both factors is trivial

If `L, M` are intermediate fields of `K'/K` and a `K`-algebra automorphism `σ` of the
compositum `L ⊔ M` fixes `L` pointwise and `M` pointwise, then `σ = 1`: the compositum is
generated over `K` by `L ∪ M` (`L ⊔ M = adjoin K (L ∪ M)`), so an automorphism fixing the
generators pointwise is the identity.
-/

namespace NK.Reconstruct

theorem eq_one_of_fixes_sup {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    (L M : IntermediateField K K') (σ : ↥(L ⊔ M) ≃ₐ[K] ↥(L ⊔ M))
    (hL : ∀ x : ↥L, σ ⟨x.1, (le_sup_left : L ≤ L ⊔ M) x.2⟩ = ⟨x.1, (le_sup_left : L ≤ L ⊔ M) x.2⟩)
    (hM : ∀ x : ↥M, σ ⟨x.1, (le_sup_right : M ≤ L ⊔ M) x.2⟩ = ⟨x.1, (le_sup_right : M ≤ L ⊔ M) x.2⟩) :
    σ = 1 := by
  -- The compositum is generated over `K` by `L ∪ M`.
  have hS : (L ⊔ M : IntermediateField K K')
      = IntermediateField.adjoin K ((L : Set K') ∪ (M : Set K')) := by
    rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self, IntermediateField.adjoin_self]
  -- It suffices to compare the two `K`-algebra homomorphisms on `L ∪ M`.
  have key : (σ : ↥(L ⊔ M) →ₐ[K] ↥(L ⊔ M)) = 1 := by
    apply IntermediateField.algHom_ext_of_eq_adjoin K hS
    intro x hx
    rcases hx with hx | hx
    · -- `x ∈ L`: use `hL` (the membership proofs are irrelevant).
      rw [show (⟨x, hS.ge (IntermediateField.subset_adjoin K _
              (Set.mem_union_left _ hx))⟩ : ↥(L ⊔ M))
            = ⟨x, (le_sup_left : L ≤ L ⊔ M) hx⟩ from Subtype.ext rfl]
      simp only [AlgHom.one_apply]
      exact hL ⟨x, hx⟩
    · -- `x ∈ M`: use `hM`.
      rw [show (⟨x, hS.ge (IntermediateField.subset_adjoin K _
              (Set.mem_union_right _ hx))⟩ : ↥(L ⊔ M))
            = ⟨x, (le_sup_right : M ≤ L ⊔ M) hx⟩ from Subtype.ext rfl]
      simp only [AlgHom.one_apply]
      exact hM ⟨x, hx⟩
  exact AlgEquiv.ext (fun x => congrFun (congrArg DFunLike.coe key) x)

end NK.Reconstruct
