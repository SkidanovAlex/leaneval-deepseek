import Mathlib
import Submission.Work.ThmF.Prove.S3.clifford_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open scoped MonoidAlgebra

namespace Work.ThmF.Prove.S3

/-- The `F`-vector space `V`, viewed as a module over `F[K]` through the restricted
representation, is Noetherian over `F[K]`: every `F[K]`-submodule is in particular an
`F`-subspace, and `V` is finite dimensional over the field `F`. -/
theorem isNoetherian_monoidAlgebra_asModule {L : Type*} [Group L] {F : Type*} [Field F]
    {K : Subgroup L} {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F L V) :
    IsNoetherian (MonoidAlgebra F K) (resRep (K := K) ρ).asModule := by
  -- `V` is Noetherian over the field `F`.
  have hF : WellFoundedGT (Submodule F (resRep (K := K) ρ).asModule) := IsNoetherian.wellFoundedGT
  -- Forgetting the `F[K]`-action gives an order embedding of the `F[K]`-submodule lattice into
  -- the `F`-subspace lattice, so well-foundedness transfers.
  have hK : WellFoundedGT (Submodule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule) :=
    (Submodule.restrictScalarsEmbedding F (MonoidAlgebra F K)
      (resRep (K := K) ρ).asModule).strictMono.wellFoundedGT
  exact isNoetherian_iff.mpr hK

theorem isotypicComponentsFinite {L : Type*} [Group L] {F : Type*} [Field F]
    {K : Subgroup L} {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F L V)
    [IsSemisimpleModule (MonoidAlgebra F K) (resRep (K := K) ρ).asModule] :
    (isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule).Finite := by
  have hnoeth := isNoetherian_monoidAlgebra_asModule (K := K) ρ
  exact Set.finite_coe_iff.mp (WellFoundedGT.finite_of_sSupIndep
    (sSupIndep_isotypicComponents (MonoidAlgebra F K) (resRep (K := K) ρ).asModule))

end Work.ThmF.Prove.S3
