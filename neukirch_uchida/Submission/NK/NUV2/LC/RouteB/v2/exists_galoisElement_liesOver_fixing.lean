import Mathlib
import Submission.NK.NUV2.LC.RouteB.level_kills_aux
import Submission.NK.HassePrinciple.LevelDictionary
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
import Submission.NK.NUV2.LC.RouteB.v2.place_smul_eq_of_apply_eq

namespace NK.NUV2.LC.RouteB.v2

/-- Existence of a Galois element fixing a level pointwise and moving one place above a place of that level to another. To be placed in namespace `NK.NUV2.LC.RouteB.v2`. Ingredients: `globalCFT_exists_smul_eq_of_liesOver` at the extension `↥M/↥L` (with `Algebra ↥L ↥M := (IntermediateField.inclusion hLM).toAlgebra` supplied by `letI`, and `haveI : IsGalois ↥L ↥M := IsGalois.tower_top_of_isGalois`), then lifting along the surjection `AlgEquiv.restrictNormalHom (K₁ := K') (E := ↥M) = levelRestrict M` (`AlgEquiv.restrictNormalHom_surjective`). -/
theorem exists_galoisElement_liesOver_fixing {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K']
    (L M : FiniteGaloisIntermediateField K K') (hLM : L ≤ M)
    {w : NK.GlobalCFT.Place ↥(L : IntermediateField K K')}
    {w₁ w₂ : NK.GlobalCFT.Place ↥(M : IntermediateField K K')}
    (h₁ : @NK.GlobalCFT.Place.LiesOver ↥(L : IntermediateField K K') _ _ ↥(M : IntermediateField K K') _ _
      ((IntermediateField.inclusion hLM).toAlgebra) w₁ w)
    (h₂ : @NK.GlobalCFT.Place.LiesOver ↥(L : IntermediateField K K') _ _ ↥(M : IntermediateField K K') _ _
      ((IntermediateField.inclusion hLM).toAlgebra) w₂ w) :
    ∃ σ : Gal(K'/K), σ ∈ L.fixingSubgroup ∧
      (NK.HassePrinciple.levelRestrict M σ) • w₁ = w₂ := by
  classical
  -- The `↥L`-algebra structure on `↥M` used by the two `LiesOver` hypotheses.
  letI : Algebra ↥(L : IntermediateField K K') ↥(M : IntermediateField K K') :=
    (IntermediateField.inclusion hLM).toAlgebra
  haveI : IsScalarTower K ↥(L : IntermediateField K K') ↥(M : IntermediateField K K') :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : FiniteDimensional ↥(L : IntermediateField K K') ↥(M : IntermediateField K K') :=
    NK.HassePrinciple.levelFiniteDimensional L M hLM
  haveI : IsGalois ↥(L : IntermediateField K K') ↥(M : IntermediateField K K') :=
    IsGalois.tower_top_of_isGalois K ↥(L : IntermediateField K K') ↥(M : IntermediateField K K')
  -- Transitivity of the Galois action on the places of `↥M` above `w`, in the extension `↥M/↥L`.
  obtain ⟨τ, hτ⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver h₁ h₂
  -- Regard `τ` as a `K`-algebra automorphism of `↥M`.
  let τ' : ↥(M : IntermediateField K K') ≃ₐ[K] ↥(M : IntermediateField K K') :=
    AlgEquiv.restrictScalars K τ
  have hτ' : τ' • w₁ = τ • w₁ :=
    place_smul_eq_of_apply_eq τ' τ (fun x => rfl) w₁
  -- Lift `τ'` to `Gal(K'/K)` along the surjective restriction map `levelRestrict M`.
  obtain ⟨σ, hσ⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥(M : IntermediateField K K')) K' τ'
  refine ⟨σ, ?_, ?_⟩
  · -- `σ` restricts to `τ'` on `↥M`, which is `↥L`-linear, so `σ` fixes `↥L` pointwise.
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hxM : x ∈ (M : IntermediateField K K') := hLM hx
    have hfixτ : τ ⟨x, hxM⟩ = ⟨x, hxM⟩ := by
      have h2 := τ.commutes' (⟨x, hx⟩ : ↥(L : IntermediateField K K'))
      exact h2
    have hmem : (NK.HassePrinciple.levelRestrict M σ) ⟨x, hxM⟩ = ⟨x, hxM⟩ := by
      rw [hσ]
      exact hfixτ
    have h3 : σ x = x := by
      have h4 := congrArg Subtype.val hmem
      simpa [AlgEquiv.restrictNormalHom_apply] using h4
    exact h3
  · rw [show NK.HassePrinciple.levelRestrict M σ = τ' from hσ]
    rw [hτ']
    exact hτ

end NK.NUV2.LC.RouteB.v2
