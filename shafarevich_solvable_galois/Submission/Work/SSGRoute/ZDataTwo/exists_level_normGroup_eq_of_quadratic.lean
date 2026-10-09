import Mathlib
import Submission.NK.LocalReciprocity.le_maxAbelianSubext_of_commutative
import Submission.NK.LocalReciprocity.NormGroup
import Submission.NK.NUV2.LC.quadraticLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Every quadratic Galois extension is a level of `F^{ab}` (up to `F`-isomorphism)

For a field `F` with a separable closure `F'` and a quadratic Galois extension `E / F`, there is a
finite normal level `Λ ≤ F^{ab} = NK.LocalReciprocity.maxAbelianSubext F F'` which is `F`-isomorphic
to `E` and has the same norm group `N_{Λ/F} Λˣ = N_{E/F} Eˣ`.

Route: `IsSepClosed.lift E` gives an `F`-algebra embedding `φ : E →ₐ[F] F'`; its image `L' ` is a
quadratic extension of `F`, hence abelian, so `L' ≤ F^{ab}` by
`NK.LocalReciprocity.le_maxAbelianSubext_of_commutative` (the Galois group is commutative because
its order is `2`, `NK.NUV2.LC.isMulCommutative_gal_of_finrank_le_two`).  Restricting `φ` to `F^{ab}`
along the inclusion `F^{ab} ↪ F'` produces the required level `Λ`, and the isomorphism `E ≃ₐ[F] ↥Λ`
transports the finite-dimensionality, normality and the norm group
(`NK.LocalReciprocity.normGroup_eq_of_algEquiv`).
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataTwo

open IntermediateField

theorem exists_level_normGroup_eq_of_quadratic {F F' : Type} [Field F] [Field F'] [Algebra F F']
    [IsSepClosure F F'] (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (hcard : Nat.card (E ≃ₐ[F] E) = 2) :
    ∃ (Λ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
      (_ : FiniteDimensional F Λ) (_ : Normal F Λ),
      Nonempty (Λ ≃ₐ[F] E) ∧
        NK.LocalReciprocity.normGroup F ↥Λ = NK.LocalReciprocity.normGroup F E := by
  -- `F'` is separably closed, so the finite separable extension `E/F` embeds into it
  haveI : IsSepClosed F' := IsSepClosure.sep_closed F
  let φ : E →ₐ[F] F' := IsSepClosed.lift (L := E)
  -- the image `L'` of `E` in `F'`
  let L' : IntermediateField F F' := φ.fieldRange
  have eφ : E ≃ₐ[F] ↥L' := AlgEquiv.ofInjectiveField φ
  -- `L'` has degree `2` over `F`, so its Galois group is commutative
  have hcardE : Module.finrank F E = 2 := by
    rw [← IsGalois.card_aut_eq_finrank, hcard]
  have hfr : Module.finrank F ↥L' ≤ 2 := by
    rw [← eφ.toLinearEquiv.finrank_eq, hcardE]
  haveI hfdL' : FiniteDimensional F ↥L' := eφ.toLinearEquiv.finiteDimensional
  haveI hgalL' : IsGalois F ↥L' := IsGalois.of_algEquiv eφ
  have hcommL' : ∀ σ τ : ↥L' ≃ₐ[F] ↥L', σ * τ = τ * σ :=
    NK.NUV2.LC.isMulCommutative_gal_of_finrank_le_two hfr
  -- hence `L'` is contained in the maximal abelian subextension of `F'`
  have hle : L' ≤ NK.LocalReciprocity.maxAbelianSubext F F' :=
    NK.LocalReciprocity.le_maxAbelianSubext_of_commutative L' hcommL'
  -- restrict `φ` to `F^{ab}` along the inclusion `F^{ab} ↪ F'`
  let A : IntermediateField F F' := NK.LocalReciprocity.maxAbelianSubext F F'
  let ψ : E →ₐ[F] A := φ.codRestrict A.toSubalgebra (fun x => hle ⟨x, rfl⟩)
  let Λ : IntermediateField F A := ψ.fieldRange
  have eψ : E ≃ₐ[F] ↥Λ := AlgEquiv.ofInjectiveField ψ
  refine ⟨Λ, eψ.toLinearEquiv.finiteDimensional, (IsGalois.of_algEquiv eψ).to_normal,
    ⟨eψ.symm⟩, ?_⟩
  exact NK.LocalReciprocity.normGroup_eq_of_algEquiv eψ.symm

end Work.SSGRoute.ZDataTwo
