import Mathlib
import Submission.Work.DSMap.Mix

namespace Work.DSEQP

universe u

open CategoryTheory

set_option linter.style.haveILetI false

/-- The homology of a cochain complex of `A`-modules which is quasi-isomorphic to a bounded-above
complex of finitely generated free `A`-modules is a finitely generated `A`-module, for `A`
Noetherian.

Suggested route: the class `QuasiIso` is at the root (no namespace); from `hφ : QuasiIso φ` one gets
`QuasiIsoAt φ j` in every degree, and `HomologicalComplex.isoOfQuasiIsoAt φ j` (or
`HomologicalComplex.isoOfQuasiIsoAt` composed with `asIso (homologyMap φ j)`) gives
`K.homology j ≅ P.homology j`.  For `P`, use `HomologicalComplex.homology i = (P.sc i).homology`
together with `ShortComplex.moduleCatHomologyIso`, which identifies `(P.sc i).homology` with
`↥(LinearMap.ker (P.d i k).hom ⧸ range (ShortComplex.moduleCatToCycles))`, a quotient of a
submodule of `P.X i`; `hP : IsBddFinFree P` gives `Module.Finite A (P.X i)`, and over the Noetherian
ring `A` submodules of a finitely generated module and their quotients are finitely generated
(`isNoetherian_of_isNoetherianRing_of_finite`, `Module.Finite.of_surjective`).  Then transport
`Module.Finite` along the isomorphism (`Module.Finite.equiv`). -/
theorem eqp_cech_homology_finite (A : Type u) [CommRing A] [IsNoetherianRing A]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : DSMap.Mix.IsBddFinFree P) (φ : P ⟶ K) (hφ : QuasiIso φ) (j : ℤ) :
    Module.Finite A (K.homology j) := by
  -- a quasi-isomorphism is an isomorphism on homology in every degree
  haveI : QuasiIso φ := hφ
  haveI : QuasiIsoAt φ j := QuasiIso.quasiIsoAt j
  -- `P.homology j` is a subquotient of the finitely generated module `P.X j`
  have hSfin : Module.Finite A ↥((P.sc j).homology) := by
    haveI : Module.Finite A ↥((P.sc j).X₂) := (hP.1 j).2
    haveI : IsNoetherian A ↥((P.sc j).X₂) :=
      isNoetherian_of_isNoetherianRing_of_finite A ↥((P.sc j).X₂)
    haveI : Module.Finite A ↥(LinearMap.ker (P.sc j).g.hom) :=
      Module.Finite.of_injective (LinearMap.ker (P.sc j).g.hom).subtype Subtype.val_injective
    have hquot : Module.Finite A ((P.sc j).g.hom.ker ⧸ (P.sc j).moduleCatToCycles.range) :=
      Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
    have hH : Module.Finite A ↥((P.sc j).moduleCatLeftHomologyData.H) := hquot
    exact Module.Finite.equiv (ShortComplex.moduleCatHomologyIso (P.sc j)).symm.toLinearEquiv
  haveI : Module.Finite A ↥(P.homology j) := hSfin
  exact Module.Finite.equiv (isoOfQuasiIsoAt φ j).toLinearEquiv

end Work.DSEQP
