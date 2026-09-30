import Mathlib
import Submission.Work.DescentGeom.DescentSetup
import Submission.Work.Descent.AffineModelAux
import Submission.Work.Descent.SpeiserEquiv
import Submission.Work.DescentGeom.chartMap_isPullback

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.DescentGeom

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory

universe u

/-- Speiser's descent statement for the charts of the quotient: for every chart `U` of the
quotient data `D.qd` (so `U.1` is a `Gal k k'`-stable affine open of `G'`), the comparison map
`D.sU U : U.1.toScheme ⟶ D.piece U`, where `D.piece U = pullback (bcπ k' D.J) (D.qd.chartι U)`
is the preimage of the chart in `J_{k'}`, is an isomorphism. -/
theorem localSpeiser {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    [FiniteDimensional k k'] (D : Work.DescentGeom.GalData k k')
    (U : (Work.DescentGeom.GalData.qd D).Chart) :
    IsIso (Work.DescentGeom.GalData.sU D U) := by
  -- The affine Speiser square: `U.1.toScheme` is the base change `chart U ×_k Spec k'`.
  have houter : IsPullback (U.1.ι ≫ D.G'.hom) ((D.qd).action.chartMap U.1 U.2.2)
      (Work.Descent.specMap k k') ((D.qd).chartι U ≫ D.J.hom) :=
    chartMap_isPullback D U
  -- Rewrite the outer square in the form suited to pasting with the base-change square of `J`.
  have houter' : IsPullback ((U.1.ι ≫ D.phi) ≫ (bc k' D.J).hom)
      ((D.qd).action.chartMap U.1 U.2.2) (Work.Descent.specMap k k')
      ((D.qd).chartι U ≫ D.J.hom) := by
    rw [Category.assoc, GalData.phi_hom']; exact houter
  -- The base-change square of `J`.
  have hright : IsPullback ((bc k' D.J).hom) (bcπ k' D.J) (Work.Descent.specMap k k')
      D.J.hom :=
    (IsPullback.of_hasPullback D.J.hom (Work.Descent.specMap k k')).flip
  have e : (U.1.ι ≫ D.phi) ≫ bcπ k' D.J
      = ((D.qd).action.chartMap U.1 U.2.2) ≫ (D.qd).chartι U := by
    rw [Category.assoc, GalData.phi_bcπ']
    exact (D.qd).quotientMap_chartι U
  -- Pasting: the local square over the chart is a pullback.
  have hleft : IsPullback (U.1.ι ≫ D.phi) ((D.qd).action.chartMap U.1 U.2.2)
      (bcπ k' D.J) ((D.qd).chartι U) :=
    (IsPullback.paste_horiz_iff hright e).mp houter'
  -- The canonical map into the pullback is `D.sU U`, hence an isomorphism.
  have key : GalData.sU D U = hleft.isoPullback.hom := by
    apply pullback.hom_ext
    · exact (GalData.sU_fst D U).trans (IsPullback.isoPullback_hom_fst hleft).symm
    · exact (GalData.sU_chart D U).trans (IsPullback.isoPullback_hom_snd hleft).symm
  rw [key]
  infer_instance

end Work.DescentGeom
