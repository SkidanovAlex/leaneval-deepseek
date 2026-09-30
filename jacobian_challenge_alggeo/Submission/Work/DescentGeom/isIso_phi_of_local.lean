import Mathlib
import Submission.Work.DescentGeom.DescentSetup
import Submission.Work.SymQuot.Chart.quotientMap_isIntegralHom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.DescentGeom

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory

universe u

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
  [IsGalois k k'] [FiniteDimensional k k']

/-- The preimage under the comparison map `D.phi` of the range of the restriction to a chart is
the chart itself. -/
lemma phi_preimage_opensRange_coverU (D : GalData k k') (U : (D.qd).Chart) :
    D.phi ⁻¹ᵁ ((D.coverU).f U).opensRange = U.1 := by
  haveI : IsOpenImmersion ((D.coverU).f U) := (D.coverU).map_prop U
  have h1 : ((D.coverU).f U).opensRange
      = bcπ k' (D.J) ⁻¹ᵁ ((D.qd).chartι U).opensRange := by
    refine TopologicalSpace.Opens.ext ?_
    rw [Scheme.Hom.coe_opensRange]
    exact IsOpenImmersion.range_pullbackFst ((D.qd).chartι U) (bcπ k' (D.J))
  rw [h1, ← Scheme.Hom.comp_preimage, D.phi_bcπ']
  exact Work.SymQuot.QuotientData.quotientMap_preimage_opensRange_chartι (D.qd) U

/-- On the range of the restriction of the cover to a chart `U`, the comparison map restricts to
the local comparison map `D.sU U`, hence is an isomorphism. -/
lemma isIso_phi_restrict (D : GalData k k') (h : ∀ U : (D.qd).Chart, IsIso (D.sU U))
    (U : (D.qd).Chart) : IsIso (D.phi ∣_ ((D.coverU).f U).opensRange) := by
  haveI : IsOpenImmersion ((D.coverU).f U) := (D.coverU).map_prop U
  have hK1 : D.phi ⁻¹ᵁ ((D.coverU).f U).opensRange = U.1 := phi_preimage_opensRange_coverU D U
  set V : (bc k' (D.J)).left.Opens := ((D.coverU).f U).opensRange with hV
  have hK1' : D.phi ⁻¹ᵁ V = U.1 := hK1
  have hrange : Set.range ⇑((D.coverU).f U) = Set.range ⇑(V.ι) := by
    rw [← Scheme.Hom.coe_opensRange V.ι, Scheme.Opens.opensRange_ι]
    exact (Scheme.Hom.coe_opensRange ((D.coverU).f U)).symm
  set e' : D.piece U ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq ((D.coverU).f U) V.ι hrange with he'
  have he'fac : e'.hom ≫ V.ι = (D.coverU).f U :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  set gam : (D.phi ⁻¹ᵁ V).toScheme ≅ U.1.toScheme :=
    Scheme.isoOfEq D.G'.left hK1' with hgam
  have hgamι : gam.inv ≫ (D.phi ⁻¹ᵁ V).ι = U.1.ι :=
    Scheme.isoOfEq_inv_ι _ hK1'
  have hkey : gam.inv ≫ (D.phi ∣_ V) = D.sU U ≫ e'.hom := by
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hgamι, ← D.sU_coverU U,
      Category.assoc, he'fac]
  have h3 : (D.phi ∣_ V) = gam.hom ≫ D.sU U ≫ e'.hom := by
    rw [show (D.phi ∣_ V) = gam.hom ≫ (gam.inv ≫ (D.phi ∣_ V)) from by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp], hkey]
  rw [h3]
  haveI := h U
  infer_instance

/-- If the local comparison maps `D.sU U` are isomorphisms for all charts `U`, then the
comparison map `D.phi : D.G'.left ⟶ (bc k' D.J).left` is an isomorphism.  The proof is that base
changing `D.phi` along the cover `D.coverU` of `(bc k' D.J).left` gives an isomorphism, because
the commuting square `D.sU U ≫ (D.coverU).f U = U.1.ι ≫ D.phi` has an isomorphism on one side,
and being an isomorphism is Zariski-local on the target. -/
theorem isIso_phi_of_local {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    [FiniteDimensional k k'] (D : Work.DescentGeom.GalData k k')
    (h : ∀ U : (Work.DescentGeom.GalData.qd D).Chart, IsIso (Work.DescentGeom.GalData.sU D U)) :
    IsIso (Work.DescentGeom.GalData.phi D) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (f := D.phi) (fun x => ?_)
  obtain ⟨U, y, hy⟩ := (D.coverU).exists_eq x
  haveI : IsOpenImmersion ((D.coverU).f U) := (D.coverU).map_prop U
  refine ⟨((D.coverU).f U).opensRange, ?_, ?_⟩
  · rw [Scheme.Hom.mem_opensRange]
    exact ⟨y, hy⟩
  · rw [MorphismProperty.isomorphisms.iff]
    exact isIso_phi_restrict D h U

end Work.DescentGeom
