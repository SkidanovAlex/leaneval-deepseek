/-
AREA DERFORMAL — construction of the derived solidification functor `L` and its counit `α`.

Given a functorial solid-cofibrant resolution `ρ` of the identity on cochain complexes of light
condensed abelian groups (`ρ K` is solid-cofibrant and `ε_K : ρ K ⟶ K` is a quasi-isomorphism,
the resolution of `Submission.Blueprint.ResolutionProp`), we show that `ρ ⋙ solC ⋙ Q` inverts
quasi-isomorphisms (`ResData.invertedBy`, using B2 and the naturality of `ε`), so that it
descends to a functor `L : D(LightCondAb) ⥤ D(Solid)` (`Localization.lift`).  Its counit
`α : Q ⋙ L ⟶ solC ⋙ Q` is the map induced by `ε`, and it is an isomorphism at every
solid-cofibrant complex (`ResData.iso_of_cofibrant`).
-/
import Submission.Work.DERFORMAL.Cofibrant

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.DERFORMAL

variable [isSolid.ι.IsRightAdjoint]

/-- Data of a functorial solid-cofibrant resolution: this is the resolution of
`Submission.Blueprint.ResolutionProp`, together with the K-projectivity of `solC` on
solid-cofibrant complexes (part (a) of B1 of REFS/02, proved in `B1KProjective`). -/
structure ResData where
  /-- the resolution functor -/
  ρ : Cpx ⥤ Cpx
  /-- the comparison with the identity -/
  ε : ρ ⟶ 𝟭 Cpx
  /-- the resolution consists of solid-cofibrant complexes -/
  hcof : ∀ K, Cofibrant (ρ.obj K)
  /-- the comparison is a quasi-isomorphism -/
  hqiso : ∀ K, QuasiIso (ε.app K)
  /-- K-projectivity of degreewise solidification of solid-cofibrant complexes -/
  hproj : ∀ K, Cofibrant K → CochainComplex.IsKProjective (solC.obj K)

namespace ResData

variable (R : ResData)

/-- The naturality of `ε : ρ ⟶ 𝟭` shows that `ρ` preserves quasi-isomorphisms. -/
theorem quasiIso_rho_map {K K' : Cpx} (f : K ⟶ K') (hf : QuasiIso f) : QuasiIso (R.ρ.map f) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso (C := LightCondAb) (R.ρ.map f)]
  have h := R.ε.naturality f
  simp only [Functor.id_obj, Functor.id_map] at h
  have h2 : Q.map (R.ρ.map f) ≫ Q.map (R.ε.app K') = Q.map (R.ε.app K) ≫ Q.map f := by
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  haveI hK : QuasiIso (R.ε.app K) := R.hqiso K
  haveI hK' : QuasiIso (R.ε.app K') := R.hqiso K'
  haveI hfQ : IsIso (Q.map f) := inferInstance
  haveI : IsIso (Q.map (R.ε.app K)) := inferInstance
  haveI : IsIso (Q.map (R.ε.app K')) := inferInstance
  haveI : IsIso (Q.map (R.ρ.map f) ≫ Q.map (R.ε.app K')) := h2 ▸ inferInstance
  exact IsIso.of_isIso_comp_right (Q.map (R.ρ.map f)) (Q.map (R.ε.app K'))

/-- `ρ ⋙ solC ⋙ Q` inverts quasi-isomorphisms (B2 applied to `ρ f`). -/
theorem invertedBy : Wq.IsInvertedBy (R.ρ ⋙ solC ⋙ Qs) := by
  intro K K' f hf
  have hf' : QuasiIso f := hf
  have h1 : QuasiIso (R.ρ.map f) := R.quasiIso_rho_map f hf'
  have h2 : QuasiIso (solC.map (R.ρ.map f)) :=
    B2 R.hproj (R.hcof K) (R.hcof K') h1
  change IsIso (Qs.map (solC.map (R.ρ.map f)))
  haveI : QuasiIso (solC.map (R.ρ.map f)) := h2
  infer_instance

/-- The comparison `ρ ⋙ solC ⟶ solC` induced by `ε`. -/
def epsSol : R.ρ ⋙ solC ⟶ solC :=
  Functor.whiskerRight R.ε solC ≫ (Functor.leftUnitor solC).hom

/-- **Derived solidification** (hole 4).  The left derived functor of degreewise solidification,
obtained by localizing the functor `ρ ⋙ solC ⋙ Q`. -/
noncomputable def L : DCat ⥤ SDCat :=
  Localization.lift (R.ρ ⋙ solC ⋙ Qs) R.invertedBy Q

/-- The comparison isomorphism `Q ⋙ L ≅ ρ ⋙ solC ⋙ Q` defining `L`. -/
noncomputable def Lfac : Q ⋙ R.L ≅ R.ρ ⋙ solC ⋙ Qs :=
  Localization.fac (R.ρ ⋙ solC ⋙ Qs) R.invertedBy Q

/-- **The counit of derived solidification** (hole 5): the natural transformation
`Q ⋙ L ⟶ solC ⋙ Q` induced by `ε`. -/
noncomputable def alpha : Q ⋙ R.L ⟶ solC ⋙ Qs :=
  R.Lfac.hom ≫ (Functor.associator R.ρ solC Qs).inv ≫ Functor.whiskerRight R.epsSol Qs

/-- The component of `alpha` at `Q K` is `Q(solC(ε_K))` (up to the isomorphism `Lfac`). -/
lemma alpha_app (K : Cpx) :
    R.alpha.app K = R.Lfac.hom.app K ≫ Qs.map (solC.map (R.ε.app K)) := by
  simp only [alpha, Lfac, NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.comp_map, epsSol, Category.assoc]
  simp

/-- **Hole 5, key property**: at a solid-cofibrant complex, the counit of derived
solidification is an isomorphism. -/
theorem iso_of_cofibrant (K : Cpx) (hK : Cofibrant K) :
    IsIso (R.alpha.app K) := by
  haveI : IsIso (R.Lfac.hom.app K) := inferInstanceAs (IsIso (R.Lfac.app K).hom)
  have h2 : QuasiIso (solC.map (R.ε.app K)) := B2 R.hproj (R.hcof K) hK (R.hqiso K)
  haveI : IsIso (Qs.map (solC.map (R.ε.app K))) := inferInstance
  rw [R.alpha_app]
  infer_instance

end ResData

end Work.DERFORMAL
