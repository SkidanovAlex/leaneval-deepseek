import Mathlib
import Submission.Work.SSGRoute.ext2_iso_cohomology
import Submission.Work.SSGRoute.ext2_iso_cohomology_proof
import Submission.Work.SSGRoute.ext2_iso_cohomology_defs
import Submission.Work.SSGRoute.groupCohomology_ihom_deg_two
import Submission.Work.SSGRoute.homRep
import Submission.Work.GroupCohomology.Basic
import Submission.Work.SSGRoute.ExtH1
import Submission.Work.SSGRoute.H1_coeff_transfer
import Submission.Work.SSGRoute.groupCohomology_one_iso_cocycles
import Submission.Work.SSGRoute.cocycles_iso_Z1
import Submission.Work.SSGRoute.e0b_core_ext
import Submission.Work.SSGRoute.stdTensorComplex_projective
import Submission.Work.SSGRoute.stdTensorAug_quasiIso
import Submission.Work.SSGRoute.stdTensorComplex_linearYonedaIso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

/-!
# Node `E1a/1` in degree one: `Ext¹_G(R, X) ≅ H¹(G, Hom_ℤ(R, X))` for a `ℤ`-lattice `R`

Degree-one companion of `Work.SSGRoute.ext2_iso_cohomology`.  The proof is the `R ⊗_ℤ`-bar
resolution argument of `Submission/Work/SSGRoute/ext2_iso_cohomology_proof.lean` with `2` replaced by
`1` throughout; every ingredient there (`stdTensorComplex`/`stdTensorAug` and its projectivity and
quasi-isomorphism, `E0bCore.extHAddEquivHomology`, `stdTensorComplex_linearYonedaIso`,
`groupCohomologyIso`) is already stated for an arbitrary degree.  The only genuinely new input is
the degree-one identification `groupCohomology_ihom_deg_one` below, whose degree-two analogue is
`Work.SSGRoute.groupCohomology_ihom_deg_two`.
-/

noncomputable section

/-- **The degree-one bridge for the internal hom.**  For `R X : Rep Coeff G`, the first group
cohomology of the internal hom `(Rep.ihom R).obj X` is the inhomogeneous `H¹` with coefficients in
the conjugation module `Hom_ℤ(R.V, X.V)`.  Assembled from `H1_coeff_transfer` (moving the two
`Coeff`-module structures on `R.V →ₗ X.V` onto each other along `bridgeEquiv`),
`groupCohomology_one_iso_cocycles` (`H¹ = Z¹/B¹`) and `cocycles_iso_Z1` (transporting `Z¹/B¹` to
the explicit crossed homomorphisms of `Work.GroupCohomology`). -/
theorem groupCohomology_ihom_deg_one (G : Type) [Group G]
    (R X : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Nonempty (groupCohomology ((Rep.ihom R).obj X) 1 ≃+
      Work.GroupCohomology.H1 G (R.V →ₗ[SSGRoute.PTExt.Coeff] X.V)) := by
  obtain ⟨e1⟩ := H1_coeff_transfer (k := SSGRoute.PTExt.Coeff) (k' := SSGRoute.PTExt.Coeff)
    (G := G) ((Rep.ihom R).obj X)
    (Rep.ofDistribMulAction SSGRoute.PTExt.Coeff G (R.V →ₗ[SSGRoute.PTExt.Coeff] X.V))
    (bridgeEquiv R X) (bridgeEquiv_rho R X)
  obtain ⟨e2⟩ := groupCohomology_one_iso_cocycles SSGRoute.PTExt.Coeff G
    (Rep.ofDistribMulAction SSGRoute.PTExt.Coeff G (R.V →ₗ[SSGRoute.PTExt.Coeff] X.V))
  obtain ⟨e3⟩ := cocycles_iso_Z1 SSGRoute.PTExt.Coeff G
    (Rep.ofDistribMulAction SSGRoute.PTExt.Coeff G (R.V →ₗ[SSGRoute.PTExt.Coeff] X.V))
    (R.V →ₗ[SSGRoute.PTExt.Coeff] X.V) (AddEquiv.refl _) (fun _ _ => rfl)
  exact ⟨e1.trans (e2.trans e3)⟩

/-- **The `Ext`-cohomology dictionary in degree one, for a `ℤ`-lattice `R`**: for a group `G`, a
`Rep Coeff G` `R` whose underlying abelian group is free and finitely generated over `ℤ`, and an
arbitrary `Rep Coeff G` `X`, `Ext¹_{ℤ[G]}(R,X) ≅ H¹(G, Hom_ℤ(R,X))`, the right-hand side being the
explicit inhomogeneous group cohomology of the internal `Hom` with the conjugation action
(`Work.SSGRoute.homRep`, `Rep.ihom`).  This is the degree-one companion of the proved
`Work.SSGRoute.ext2_iso_cohomology`; the `R ⊗_ℤ` bar-resolution proof of the degree-two statement
(`Submission/Work/SSGRoute/ext2_iso_cohomology_proof.lean`) applies verbatim in degree one — the one
missing ingredient is a degree-one version of `Work.SSGRoute.groupCohomology_ihom_deg_two` (the
identification `groupCohomology ((Rep.ihom R).obj X) 1 ≅ Work.GroupCohomology.H1 G (R.V →ₗ X.V)`,
whose degree-two analogue is proved in `Submission/Work/SSGRoute/groupCohomology_ihom_deg_two.lean`
out of `H2_coeff_transfer`, `groupCohomology_two_iso_cocycles` and `cocycles_iso_Z2`). -/
theorem ext_one_iso_lattice_cohomology (G : Type) [Group G] (R X : Rep.{0} SSGRoute.PTExt.Coeff G)
    [Module.Free ℤ R.V] [Module.Finite ℤ R.V] :
    Nonempty (CategoryTheory.Abelian.Ext R X 1 ≃+
      Work.GroupCohomology.H1 G (R.V →ₗ[SSGRoute.PTExt.Coeff] X.V)) := by
  classical
  -- the projective resolution `C_• ⊗ R` of `R`
  have hqi : QuasiIso (stdTensorAug G R) := stdTensorAug_quasiIso G R
  let P : ProjectiveResolution R :=
    { complex := stdTensorComplex G R
      projective := fun n => stdTensorComplex_projective G R n
      π := stdTensorAug G R
      quasiIso := hqi }
  -- `Ext¹_G(R,X)` is the first homology of `Hom_G(P_•, X)`
  obtain ⟨Φ, _⟩ := E0bCore.extHAddEquivHomology (C := Rep.{0} SSGRoute.PTExt.Coeff G)
    (k := SSGRoute.PTExt.Coeff) (X := R) (Y := X) P 1
  -- tensor–hom: the `Hom`-complex of `P_•` is the `Hom`-complex of the bar resolution with
  -- coefficients in `R ⟹ X`
  obtain ⟨e⟩ := stdTensorComplex_linearYonedaIso G R X
  have h2 : (P.complex.linearYonedaObj SSGRoute.PTExt.Coeff X).homology 1 ≃+
      ((Rep.barResolution SSGRoute.PTExt.Coeff G).complex.linearYonedaObj
        SSGRoute.PTExt.Coeff ((Rep.ihom R).obj X)).homology 1 :=
    ((HomologicalComplex.homologyFunctor (ModuleCat.{0} SSGRoute.PTExt.Coeff)
        (ComplexShape.up ℕ) 1).mapIso e).toLinearEquiv.toAddEquiv
  -- the bar resolution computes group cohomology
  have h3 : groupCohomology ((Rep.ihom R).obj X) 1 ≃+
      ((Rep.barResolution SSGRoute.PTExt.Coeff G).complex.linearYonedaObj
        SSGRoute.PTExt.Coeff ((Rep.ihom R).obj X)).homology 1 :=
    (groupCohomologyIso ((Rep.ihom R).obj X) 1
      (Rep.barResolution SSGRoute.PTExt.Coeff G)).toLinearEquiv.toAddEquiv
  -- Mathlib's group cohomology in degree one is the explicit inhomogeneous `H¹`
  obtain ⟨c⟩ := groupCohomology_ihom_deg_one G R X
  exact ⟨Φ.symm.trans (h2.trans (h3.symm.trans c))⟩

end

end Work.SSGRoute
