import Mathlib
import Submission.Work.DescentGeom.DescentSetup
import Submission.Work.Descent.AffineModelAux
import Submission.Work.Descent.SpeiserEquiv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.DescentGeom

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory TensorProduct

universe u

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace GalData

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
  [FiniteDimensional k k']

/-- The `k'`-algebra structure on the sections over a chart, induced by the structure morphism
`G' ⟶ Spec k'` of `G'`. -/
instance instAlgebraSectionsK' (D : GalData k k') (U : (D.qd).Chart) :
    Algebra k' Γ(D.G'.left, U.1) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k')).inv ≫
    Scheme.Hom.appLE D.G'.hom ⊤ U.1 (le_top)).hom.toAlgebra

/-- The `k`-algebra structure on the sections over a chart, induced by the structure morphism
`strK : G' ⟶ Spec k`. -/
instance instAlgebraSectionsK (D : GalData k k') (U : (D.qd).Chart) :
    Algebra k Γ(D.G'.left, U.1) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    Scheme.Hom.appLE D.strK ⊤ U.1 (le_top)).hom.toAlgebra

/-- The structure morphism of the affine chart `Spec Γ(G',U) ⟶ Spec k'` is `Spec` of the
canonical `k'`-algebra structure on `Γ(G',U)`. -/
lemma fromSpec_comp_hom (D : GalData k k') (U : (D.qd).Chart) :
    U.2.1.fromSpec ≫ D.G'.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k' Γ(D.G'.left, U.1))) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (f := D.G'.hom)
    (U := (⊤ : (Spec (CommRingCat.of k')).Opens)) (V := U.1)
    (isAffineOpen_top (Spec (CommRingCat.of k'))) U.2.1 (le_top)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]
  rfl

/-- The structure morphism of the affine chart `Spec Γ(G',U) ⟶ Spec k` is `Spec` of the
canonical `k`-algebra structure on `Γ(G',U)`. -/
lemma fromSpec_comp_strK (D : GalData k k') (U : (D.qd).Chart) :
    U.2.1.fromSpec ≫ D.strK =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(D.G'.left, U.1))) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec (f := D.strK)
    (U := (⊤ : (Spec (CommRingCat.of k)).Opens)) (V := U.1)
    (isAffineOpen_top (Spec (CommRingCat.of k))) U.2.1 (le_top)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← h, ← Spec.map_comp]
  rfl

/-- **The affine chart over `Spec k'`.**  The inclusion `U.1.toScheme ⟶ G'` followed by the
structure morphism of `G'` is `Spec` of the `k'`-algebra structure on the sections. -/
lemma toSpecΓ_algebraMap_sections (D : GalData k k') (U : (D.qd).Chart) :
    U.1.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k' Γ(D.G'.left, U.1))) =
      U.1.ι ≫ D.G'.hom := by
  rw [← fromSpec_comp_hom D U, ← Category.assoc, ← IsAffineOpen.isoSpec_hom U.2.1,
    IsAffineOpen.isoSpec_hom_fromSpec]

/-- **The affine chart over `Spec k`.**  The inclusion `U.1.toScheme ⟶ G'` followed by the
structure morphism `strK` of `G'` over `Spec k` is `Spec` of the `k`-algebra structure on the
sections. -/
lemma toSpecΓ_algebraMap_sections_strK (D : GalData k k') (U : (D.qd).Chart) :
    U.1.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap k Γ(D.G'.left, U.1))) =
      U.1.ι ≫ D.strK := by
  rw [← fromSpec_comp_strK D U, ← Category.assoc, ← IsAffineOpen.isoSpec_hom U.2.1,
    IsAffineOpen.isoSpec_hom_fromSpec]

/-- The scalar tower `k ⟶ k' ⟶ Γ(G',U)`. -/
instance instIsScalarTowerSections (D : GalData k k') (U : (D.qd).Chart) :
    IsScalarTower k k' Γ(D.G'.left, U.1) := by
  apply IsScalarTower.of_algebraMap_eq'
  have hcomp : CommRingCat.ofHom ((algebraMap k' Γ(D.G'.left, U.1)).comp (algebraMap k k')) =
      CommRingCat.ofHom (algebraMap k k') ≫
        CommRingCat.ofHom (algebraMap k' Γ(D.G'.left, U.1)) :=
    CommRingCat.ofHom_comp _ _
  have hmain : Spec.map (CommRingCat.ofHom (algebraMap k Γ(D.G'.left, U.1))) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap k' Γ(D.G'.left, U.1)).comp (algebraMap k k'))) := by
    rw [hcomp, Spec.map_comp, ← fromSpec_comp_strK, ← fromSpec_comp_hom]
    rw [show Spec.map (CommRingCat.ofHom (algebraMap k k')) = Work.Descent.specMap k k' from rfl]
    rw [strK, Category.assoc]
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective hmain)
  simpa only [CommRingCat.hom_ofHom] using this

/-- The ring automorphism of the sections induced by `σ`, as the inverse of `sectionHom σ`
(the `GAction` convention is contravariant). -/
def sectEquiv (D : GalData k k') (U : (D.qd).Chart) (σ : Work.Descent.Gal k k') :
    Γ(D.G'.left, U.1) ≃+* Γ(D.G'.left, U.1) where
  toFun := Work.SymQuot.GAction.sectionHom (D.qd).action U.1 U.2.2 σ⁻¹
  invFun := Work.SymQuot.GAction.sectionHom (D.qd).action U.1 U.2.2 σ
  left_inv x := by
    rw [← RingHom.comp_apply,
      ← Work.SymQuot.GAction.sectionHom_mul (D.qd).action U.1 U.2.2 σ⁻¹ σ]
    simp
  right_inv x := by
    rw [← RingHom.comp_apply,
      ← Work.SymQuot.GAction.sectionHom_mul (D.qd).action U.1 U.2.2 σ σ⁻¹]
    simp
  map_add' := map_add _
  map_mul' := map_mul _

/-- The Galois action on the sections `Γ(G',U)`, as a monoid homomorphism to ring automorphisms.
-/
def galActRingEquiv (D : GalData k k') (U : (D.qd).Chart) :
    Work.Descent.Gal k k' →* (Γ(D.G'.left, U.1) ≃+* Γ(D.G'.left, U.1)) where
  toFun := sectEquiv D U
  map_one' := by
    ext x
    show Work.SymQuot.GAction.sectionHom (D.qd).action U.1 U.2.2
      (1 : Work.Descent.Gal k k')⁻¹ x = x
    simp
  map_mul' σ τ := by
    ext x
    show Work.SymQuot.GAction.sectionHom (D.qd).action U.1 U.2.2 (σ * τ)⁻¹ x =
      Work.SymQuot.GAction.sectionHom (D.qd).action U.1 U.2.2 σ⁻¹
        (Work.SymQuot.GAction.sectionHom (D.qd).action U.1 U.2.2 τ⁻¹ x)
    rw [mul_inv_rev, ← RingHom.comp_apply,
      ← Work.SymQuot.GAction.sectionHom_mul (D.qd).action U.1 U.2.2 τ⁻¹ σ⁻¹]

/-- **Semilinearity.**  The action of `σ` on the sections sends the `k'`-structure constants
`c` to `σ c`. -/
lemma galActRingEquiv_algebraMap (D : GalData k k') (U : (D.qd).Chart)
    (σ : Work.Descent.Gal k k') (c : k') :
    galActRingEquiv D U σ (algebraMap k' Γ(D.G'.left, U.1) c) =
      algebraMap k' Γ(D.G'.left, U.1) (σ c) := by
  show Work.SymQuot.GAction.sectionHom (D.qd).action U.1 U.2.2 σ⁻¹
      (algebraMap k' Γ(D.G'.left, U.1) c) = algebraMap k' Γ(D.G'.left, U.1) (σ c)
  rw [show (algebraMap k' Γ(D.G'.left,U.1)) =
      ((Scheme.ΓSpecIso (CommRingCat.of k')).inv ≫
        Scheme.Hom.appLE D.G'.hom ⊤ U.1 (le_top)).hom from RingHom.algebraMap_toAlgebra _]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Work.SymQuot.GAction.sectionHom_apply]
  have hact : D.qd.action.hom σ⁻¹ = (D.galAct σ).hom := by
    rw [qd_action, act_hom, inv_inv]
  have h1 : Scheme.Hom.appLE D.G'.hom ⊤ U.1 (le_top : U.1 ≤ D.G'.hom ⁻¹ᵁ ⊤) ≫
        Scheme.Hom.appLE (D.qd.action.hom σ⁻¹) U.1 U.1 (le_of_eq (U.2.2 σ⁻¹).symm)
      = Scheme.Hom.appLE (specGal σ) ⊤ ⊤ (le_top : ⊤ ≤ (specGal σ) ⁻¹ᵁ ⊤) ≫
        Scheme.Hom.appLE D.G'.hom ⊤ U.1 (le_top : U.1 ≤ D.G'.hom ⁻¹ᵁ ⊤) := by
    rw [Scheme.Hom.appLE_comp_appLE]
    rw [Scheme.Hom.appLE_comp_appLE]
    exact Work.SymQuot.appLE_congr_hom (by rw [hact, D.hhom σ]) _ _
  have hnat : (Scheme.Hom.appLE (specGal σ) ⊤ ⊤ (le_top : ⊤ ≤ (specGal σ) ⁻¹ᵁ ⊤)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of k')).inv.hom c)
      = (Scheme.ΓSpecIso (CommRingCat.of k')).inv.hom (σ c) := by
    have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : k' →+* k'))
    have h2 := congrArg (fun (f : CommRingCat.of k' ⟶ Γ(Spec (CommRingCat.of k'), ⊤)) =>
      f.hom c) h
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE] at h2
    exact h2.symm
  rw [← CommRingCat.comp_apply, h1, CommRingCat.comp_apply, hnat]

/-- The semilinear Galois action on the sections over a chart. -/
def galSemilinear (D : GalData k k') (U : (D.qd).Chart) :
    Work.Descent.SemilinearAction k k' Γ(D.G'.left, U.1) where
  act := galActRingEquiv D U
  act_smul σ c b := by
    show galActRingEquiv D U σ (algebraMap k' Γ(D.G'.left,U.1) c * b) =
      algebraMap k' Γ(D.G'.left,U.1) (σ c) * galActRingEquiv D U σ b
    rw [map_mul, galActRingEquiv_algebraMap]

/-- The comparison isomorphism `U.1.toScheme ≅ Spec (Γ(G',U)^Γ ⊗_k k')`, from the inverse of the
Speiser equivalence. -/
def chartBaseChangeIso (D : GalData k k') (U : (D.qd).Chart) :
    U.1.toScheme ≅ Spec (CommRingCat.of (↥(galSemilinear D U).invariants ⊗[k] k')) := by
  haveI : IsIso (Spec.map (CommRingCat.ofHom
      ((galSemilinear D U).speiserRingEquiv.toRingHom))) :=
    (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
      (galSemilinear D U).speiserRingEquiv).op).isIso_hom
  exact U.2.1.isoSpec ≪≫
    asIso (Spec.map (CommRingCat.ofHom ((galSemilinear D U).speiserRingEquiv.toRingHom)))

/-- Speiser's equivalence followed by the inclusion of the invariants. -/
lemma speiser_subtype (D : GalData k k') (U : (D.qd).Chart) :
    (galSemilinear D U).speiserRingEquiv.toRingHom.comp
        (algebraMap ↥(galSemilinear D U).invariants
          (↥(galSemilinear D U).invariants ⊗[k] k')) =
      Subring.subtype (galSemilinear D U).invariants.toSubring := by
  ext a
  simp [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_def, Algebra.smul_def]

/-- Speiser's equivalence restricted to `k'` is the `k'`-algebra structure. -/
lemma speiser_includeRight (D : GalData k k') (U : (D.qd).Chart) :
    (galSemilinear D U).speiserRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := k) (A := ↥(galSemilinear D U).invariants)
        (B := k')).toRingHom =
      algebraMap k' Γ(D.G'.left, U.1) := by
  ext a
  simp [RingHom.comp_apply, Algebra.TensorProduct.includeRight, Algebra.smul_def]

/-- The comparison isomorphism is compatible with the chart maps. -/
lemma chartBaseChangeIso_chartMap (D : GalData k k') (U : (D.qd).Chart) :
    (chartBaseChangeIso D U).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap ↥(galSemilinear D U).invariants
          (↥(galSemilinear D U).invariants ⊗[k] k'))) =
      (D.qd).action.chartMap U.1 U.2.2 := by
  show (U.2.1.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      ((galSemilinear D U).speiserRingEquiv.toRingHom))) ≫ _ = _
  rw [IsAffineOpen.isoSpec_hom, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    speiser_subtype]
  rfl

/-- The comparison isomorphism is compatible with the structure morphisms to `Spec k'`. -/
lemma chartBaseChangeIso_structK' (D : GalData k k') (U : (D.qd).Chart) :
    (chartBaseChangeIso D U).hom ≫ Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight (R := k) (A := ↥(galSemilinear D U).invariants)
          (B := k')).toRingHom)) =
      U.1.ι ≫ D.G'.hom := by
  show (U.2.1.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      ((galSemilinear D U).speiserRingEquiv.toRingHom))) ≫ _ = _
  rw [IsAffineOpen.isoSpec_hom, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    speiser_includeRight]
  exact toSpecΓ_algebraMap_sections D U

/-- **The structure morphism of the chart over `Spec k`.**  The chart inclusion followed by the
structure morphism of the quotient `J` over `Spec k` is `Spec` of the `k`-algebra structure on the
invariants of the sections. -/
lemma chartι_algebraMap (D : GalData k k') (U : (D.qd).Chart) :
    Spec.map (CommRingCat.ofHom (algebraMap k ↥(galSemilinear D U).invariants)) =
      (D.qd).chartι U ≫ D.J.hom := by
  letI : MulSemiringAction (Work.Descent.Gal k k') Γ(D.G'.left, U.1) :=
    (D.qd).action.sectionMulSemiringAction U.1 U.2.2
  set hU : Spec (CommRingCat.of ↥Γ(D.G'.left, U.1)) ⟶ Spec (CommRingCat.of k) :=
    U.2.1.isoSpec.inv ≫ (U.1.ι ≫ D.strK) with hU_def
  have hinv : ∀ g : Work.Descent.Gal k k',
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (Work.Descent.Gal k k')
        ↥Γ(D.G'.left, U.1) g)) ≫ hU = hU := by
    intro g
    rw [hU_def, Work.SymQuot.Chart.toRingHom_eq_sectionHom (D.qd).action U.2.2 g,
      Work.SymQuot.Chart.spec_map_sectionHom (D.qd).action U.2.1 U.2.2 g]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι_assoc,
      show D.qd.action.hom g⁻¹ = D.act.hom g⁻¹ from rfl, D.strK_invariant g⁻¹]
  obtain ⟨gU, hgU, huniq⟩ :=
    Work.SymQuot.Chart.existsUnique_affine_target (G := Work.Descent.Gal k k') hU hinv
  have hchart : Spec.map (CommRingCat.ofHom (Subring.subtype
      (FixedPoints.subring ↥Γ(D.G'.left, U.1) (Work.Descent.Gal k k')))) ≫
      ((D.qd).chartι U ≫ D.J.hom) = hU := by
    have hq : (D.qd).quotientMap ≫ D.J.hom = D.strK := D.q_hom
    have h1 : (U.2.1.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Subring.subtype
        (FixedPoints.subring ↥Γ(D.G'.left, U.1) (Work.Descent.Gal k k'))))) ≫
        ((D.qd).chartι U ≫ D.J.hom) = U.1.ι ≫ D.strK := by
      rw [IsAffineOpen.isoSpec_hom, ← Work.SymQuot.GAction.chartMap, ← Category.assoc,
        ← Work.SymQuot.QuotientData.quotientMap_chartι (D.qd) U, Category.assoc, hq]
    rw [hU_def, ← h1]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc]
  have hmine : Spec.map (CommRingCat.ofHom (Subring.subtype
      (FixedPoints.subring ↥Γ(D.G'.left, U.1) (Work.Descent.Gal k k')))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k ↥(galSemilinear D U).invariants)) = hU := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hsub : (Subring.subtype (galSemilinear D U).invariants.toSubring).comp
        (algebraMap k ↥(galSemilinear D U).invariants) = algebraMap k ↥Γ(D.G'.left, U.1) := by
      ext c; exact Subalgebra.coe_algebraMap (galSemilinear D U).invariants c
    rw [show (Subring.subtype (FixedPoints.subring ↥Γ(D.G'.left,U.1) (Work.Descent.Gal k k'))).comp
        (algebraMap k ↥(galSemilinear D U).invariants) =
      algebraMap k ↥Γ(D.G'.left, U.1) from hsub, hU_def,
      ← toSpecΓ_algebraMap_sections_strK D U, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_toSpecΓ]
    rfl
  exact (huniq _ hmine).trans (huniq _ hchart).symm

end GalData

end

theorem chartMap_isPullback {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    [FiniteDimensional k k'] (D : Work.DescentGeom.GalData k k')
    (U : (Work.DescentGeom.GalData.qd D).Chart) :
    IsPullback (U.1.ι ≫ D.G'.hom) ((Work.DescentGeom.GalData.qd D).action.chartMap U.1 U.2.2)
      (Work.Descent.specMap k k')
      ((Work.DescentGeom.GalData.qd D).chartι U ≫ D.J.hom) := by
  have hpb := Work.Descent.AffineModelAux.isPullback_specTensor (k := k) (k' := k')
    (↥(GalData.galSemilinear D U).invariants)
  refine (IsPullback.of_iso hpb
    (GalData.chartBaseChangeIso D U).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_).flip
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [Iso.symm_hom, ← GalData.chartBaseChangeIso_chartMap D U, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    rw [← GalData.chartBaseChangeIso_structK' D U, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id]
    exact GalData.chartι_algebraMap D U
  · simp

end Work.DescentGeom
