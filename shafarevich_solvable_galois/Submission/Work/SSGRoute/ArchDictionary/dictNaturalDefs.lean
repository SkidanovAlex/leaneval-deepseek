import Mathlib
import Submission.Work.SSGRoute.ExtOnePre
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `homRepPre` is equivariant

The map `homRepPre M M' N u : homRep M N ⟶ homRep M' N` induced by `u : M' ⟶ M` on the internal
`Hom` (postcomposition with `u` on the argument) is a morphism of `G`-representations, hence its
underlying additive map is `Work.GroupCohomology.IsEquivariant`.  This is the map that appears in
the coefficient-naturality square of the divisible-coefficient `Ext¹ ↔ H¹` dictionary
(`Work.SSGRoute.ArchDictionary.extOneDictNatural`).

The instance `homRepDistribMulAction` is written out explicitly (type-class search does not unfold
the `def homRep`), which is why the statement below is spelled with `X.V →ₗ[Coeff] N.V` rather than
`↑(homRep X N)`.
-/

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

variable {G : Type} [Group G]

/-- `homRepPre` is `G`-equivariant for the conjugation action on the internal hom. -/
theorem homRepPre_isEquivariant (X X' N : Rep.{0} Coeff G) (u : X' ⟶ X) :
    @Work.GroupCohomology.IsEquivariant G (X.V →ₗ[Coeff] N.V) (X'.V →ₗ[Coeff] N.V) _ _ _
      (homRepDistribMulAction X N) (homRepDistribMulAction X' N)
      (homRepPre X X' N u).hom.toAddMonoidHom := by
  intro g ψ
  show (show X'.V →ₗ[Coeff] N.V from (homRepPre X X' N u).hom (g • ψ))
      = (g • (show X'.V →ₗ[Coeff] N.V from (homRepPre X X' N u).hom ψ))
  ext x
  rw [homRepPre_apply X X' N u (g • ψ) x]
  rw [homRep_smul_apply X N g ψ (u.hom x)]
  rw [homRep_smul_apply X' N g (show X'.V →ₗ[Coeff] N.V from (homRepPre X X' N u).hom ψ) x]
  rw [homRepPre_apply X X' N u ψ (X'.ρ g⁻¹ x)]
  rw [Rep.hom_comm_apply u g⁻¹ x]

/-- `H¹(G, Hom_ℤ(M,N))` with the *conjugation* action on the internal hom `Hom_ℤ(M,N)`.

Named (`abbrev`, so reducible) because type-class search does not unfold the `def homRep`, so that
`Work.GroupCohomology.H1 G (M.V →ₗ[Coeff] N.V)` cannot find `homRepDistribMulAction`. -/
abbrev homH1 (G : Type) [Group G] (M N : Rep.{0} Coeff G) : Type :=
  @Work.GroupCohomology.H1 G (M.V →ₗ[Coeff] N.V) _ _ (homRepDistribMulAction M N)

/-- The map `H¹(G, Hom_ℤ(M,N)) → H¹(G, Hom_ℤ(M',N))` induced by `u : M' ⟶ M`. -/
noncomputable abbrev homMapH1 (G : Type) [Group G] (M M' N : Rep.{0} Coeff G) (u : M' ⟶ M) :
    homH1 G M N →+ homH1 G M' N :=
  @Work.GroupCohomology.mapH1 G (M.V →ₗ[Coeff] N.V) (M'.V →ₗ[Coeff] N.V) _ _ _
    (homRepDistribMulAction M N) (homRepDistribMulAction M' N)
    (homRepPre M M' N u).hom.toAddMonoidHom (homRepPre_isEquivariant M M' N u)

end Work.SSGRoute
