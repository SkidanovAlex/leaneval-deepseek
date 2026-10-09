import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.homRep
import Submission.Work.GroupCohomology.Basic
import Submission.Work.SSGRoute.ext2_iso_cohomology_defs
import Submission.Work.SSGRoute.e0b_core_ext
import Submission.Work.SSGRoute.stdTensorComplex_projective
import Submission.Work.SSGRoute.stdTensorAug_quasiIso
import Submission.Work.SSGRoute.stdTensorComplex_linearYonedaIso
import Submission.Work.SSGRoute.groupCohomology_ihom_deg_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node `E1a/1` (proved): `Ext²_G(R,X) ≅ H²(G, Hom_ℤ(R,X))` for a `ℤ`-lattice `R`

For a group `G`, a `ℤ`-lattice `R = R.V` with a `G`-action (i.e. `R : Rep ℤ G` whose underlying
abelian group is free) and an arbitrary `Rep ℤ G` `X`, the second `Ext`-group of `R` with
coefficients in `X` is the second group cohomology of the internal hom `Hom_ℤ(R,X)`
(`Rep.ihom R X`, i.e. `R.V →ₗ[ℤ] X.V` with the conjugation action `g · f = ρ_X g ∘ f ∘ ρ_R g⁻¹`).

The proof assembles four pieces:

* `stdTensorComplex`/`stdTensorAug` (`SSGRoute/ext2_iso_cohomology_defs`): the image of Mathlib's
  bar resolution of the trivial module `ℤ` under the (exact) functor `- ⊗_ℤ R`, with its
  augmentation `ε ⊗ id`.  `stdTensorComplex_projective` and `stdTensorAug_quasiIso` show that it is
  a projective resolution of `R`.
* `E0bCore.extHAddEquivHomology`: for *any* projective resolution `P` of `R`, `Extⁿ_G(R,X)` is the
  `n`-th homology of the complex `Hom_G(P_•, X)` (via `ProjectiveResolution.extMk`).
* `stdTensorComplex_linearYonedaIso`: the tensor–hom adjunction of the closed monoidal structure of
  `Rep ℤ G` identifies this complex with `Hom_G(C_•, R ⟹ X)`, the complex of the bar resolution with
  coefficients in the internal hom.
* `groupCohomologyIso` (Mathlib) identifies the homology of *that* complex with Mathlib's
  `groupCohomology`, and `groupCohomology_ihom_deg_two` identifies Mathlib's construction in degree
  `2` with the explicit inhomogeneous-cochain `H²` used by this project
  (`Work.GroupCohomology.H2`).
-/

namespace Work.SSGRoute

open CategoryTheory

noncomputable section

theorem ext2_iso_cohomology_proof (G : Type) [Group G] (R X : Rep.{0} SSGRoute.PTExt.Coeff G)
    [Module.Free ℤ R.V] [Module.Finite ℤ R.V] :
    Nonempty (CategoryTheory.Abelian.Ext R X 2 ≃+
      Work.GroupCohomology.H2 G (R.V →ₗ[SSGRoute.PTExt.Coeff] X.V)) := by
  classical
  -- the projective resolution `C_• ⊗ R` of `R`
  have hqi : QuasiIso (stdTensorAug G R) := stdTensorAug_quasiIso G R
  let P : ProjectiveResolution R :=
    { complex := stdTensorComplex G R
      projective := fun n => stdTensorComplex_projective G R n
      π := stdTensorAug G R
      quasiIso := hqi }
  -- `Ext²_G(R,X)` is the second homology of `Hom_G(P_•, X)`
  obtain ⟨Φ, _⟩ := E0bCore.extHAddEquivHomology (C := Rep.{0} SSGRoute.PTExt.Coeff G)
    (k := SSGRoute.PTExt.Coeff) (X := R) (Y := X) P 2
  -- tensor–hom: the `Hom`-complex of `P_•` is the `Hom`-complex of the bar resolution with
  -- coefficients in `R ⟹ X`
  obtain ⟨e⟩ := stdTensorComplex_linearYonedaIso G R X
  have h2 : (P.complex.linearYonedaObj SSGRoute.PTExt.Coeff X).homology 2 ≃+
      ((Rep.barResolution SSGRoute.PTExt.Coeff G).complex.linearYonedaObj
        SSGRoute.PTExt.Coeff ((Rep.ihom R).obj X)).homology 2 :=
    ((HomologicalComplex.homologyFunctor (ModuleCat.{0} SSGRoute.PTExt.Coeff)
        (ComplexShape.up ℕ) 2).mapIso e).toLinearEquiv.toAddEquiv
  -- the bar resolution computes group cohomology
  have h3 : groupCohomology ((Rep.ihom R).obj X) 2 ≃+
      ((Rep.barResolution SSGRoute.PTExt.Coeff G).complex.linearYonedaObj
        SSGRoute.PTExt.Coeff ((Rep.ihom R).obj X)).homology 2 :=
    (groupCohomologyIso ((Rep.ihom R).obj X) 2
      (Rep.barResolution SSGRoute.PTExt.Coeff G)).toLinearEquiv.toAddEquiv
  -- Mathlib's group cohomology in degree two is the explicit inhomogeneous `H²`
  obtain ⟨c⟩ := groupCohomology_ihom_deg_two G R X
  exact ⟨Φ.symm.trans (h2.trans (h3.symm.trans c))⟩

end

end Work.SSGRoute
