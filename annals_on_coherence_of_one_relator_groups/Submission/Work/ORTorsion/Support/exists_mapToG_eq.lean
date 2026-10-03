import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Support

open scoped TensorProduct
open Work.ORTorsion

variable {K : Type*} [Field K] {G : Type*} [Group G] {H : Subgroup G}

/-- `mapToG H` agrees with the monoid-algebra map induced by the inclusion `H ↪ G`. -/
theorem mapToG_eq_mapDomainAlgHom (K : Type*) [Field K] (G : Type*) [Group G] (H : Subgroup G) :
    mapToG (K := K) (G := G) H = MonoidAlgebra.mapDomainAlgHom K K H.subtype := by
  unfold mapToG
  rw [MonoidAlgebra.lift_unique' (MonoidAlgebra.mapDomainAlgHom K K H.subtype)]
  congr 1
  ext h
  simp [MonoidAlgebra.mapDomainAlgHom_apply]

/-- The coefficient of `mapToG H y` at `g ∈ G` is the sum of the coefficients of `y` over the
preimage of `g`.  In particular `mapToG H` is given by `MonoidAlgebra.mapDomain` along the
inclusion of `H` in `G`. -/
theorem coeff_mapToG (y : MonoidAlgebra K H) :
    (mapToG H y).coeff = Finsupp.mapDomain (⇑H.subtype) y.coeff := by
  rw [mapToG_eq_mapDomainAlgHom K G H, MonoidAlgebra.mapDomainAlgHom_apply]
  rfl

/-- An element `β` of `K[G]` whose support is contained in a subgroup `H` is in the image of the
natural map `K[H] → K[G]`. -/
theorem exists_mapToG_eq {K : Type*} [Field K] {G : Type*} [Group G] {H : Subgroup G}
    (β : MonoidAlgebra K G) (hβ : ∀ g ∈ β.coeff.support, g ∈ H) :
    ∃ x : MonoidAlgebra K H, mapToG H x = β := by
  classical
  have hf : Function.Injective (⇑H.subtype) := fun a b h => Subtype.ext h
  have hx : ↑β.coeff.support ⊆ Set.range ⇑(H.subtype) := by
    intro g hg
    exact ⟨⟨g, hβ g hg⟩, rfl⟩
  refine ⟨MonoidAlgebra.comapDomain H.subtype hf β, ?_⟩
  rw [mapToG_eq_mapDomainAlgHom, MonoidAlgebra.mapDomainAlgHom_apply]
  exact MonoidAlgebra.mapDomain_comapDomain hx hf

end Work.ORTorsion.Support
