/-
AREA DERFORMAL — holes 4–7: setup of the adjunctions at the level of complexes and of
the homotopy category.

We record:
* `solCAdj : solC ⊣ incC`, the degreewise solidification adjunction on cochain complexes;
* `solKAdj : solK ⊣ incK`, the induced adjunction on homotopy categories;
* the comparison isomorphisms `solKFactorsIso`, `incKFactorsIso` between the homotopy-category
  functors `solK`, `incK` and the quotient functors;
* `homKEquiv`, the resulting bijection
  `Hom_K(solC K, N) ≃ Hom_K(K, incC N)` together with its naturality in `K`;
* the fact that `incC` both preserves and reflects quasi-isomorphisms.
-/
import Submission.Work.DERFORMAL.Basic
import Submission.Work.DERFORMAL.Gen.AdjHomologicalComplex
import Submission.Work.DERFORMAL.Gen.AdjHomotopyCategory

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.unusedSectionVars false

namespace Work.DERFORMAL

variable [isSolid.ι.IsRightAdjoint]

/-- The quotient functor `C(LightCondAb) ⥤ K(LightCondAb)`. -/
abbrev qc : Cpx ⥤ KCat := HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)

/-- The quotient functor `C(Solid) ⥤ K(Solid)`. -/
abbrev qs : SCpx ⥤ SKCat := HomotopyCategory.quotient Solid (ComplexShape.up ℤ)

/-- The degreewise adjunction `solC ⊣ incC` on cochain complexes. -/
noncomputable def solCAdj : solC ⊣ incC :=
  Classical.choice (Gen.AdjHomologicalComplex slAdj (ComplexShape.up ℤ))

/-- The adjunction `solK ⊣ incK` on homotopy categories induced by solidification. -/
noncomputable def solKAdj : solK ⊣ incK :=
  Classical.choice (Gen.AdjHomotopyCategory slAdj (ComplexShape.up ℤ))

/-- The natural isomorphism `qc ⋙ solK ≅ solC ⋙ qs`. -/
noncomputable def solKFactorsIso : qc ⋙ solK ≅ solC ⋙ qs :=
  Functor.mapHomotopyCategoryFactors sl (ComplexShape.up ℤ)

/-- The natural isomorphism `qs ⋙ incK ≅ incC ⋙ qc`. -/
noncomputable def incKFactorsIso : qs ⋙ incK ≅ incC ⋙ qc :=
  Functor.mapHomotopyCategoryFactors isSolid.ι (ComplexShape.up ℤ)

/-- The comparison isomorphism `solK (hq K) ≅ hs (solC K)`. -/
noncomputable def solKFactors (K : Cpx) : solK.obj (hq K) ≅ hs (solC.obj K) :=
  solKFactorsIso.app K

/-- The comparison isomorphism `incK (hs K) ≅ hq (incC K)`. -/
noncomputable def incKFactors (K : SCpx) : incK.obj (hs K) ≅ hq (incC.obj K) :=
  incKFactorsIso.app K

/-- Naturality of `solKFactors` (in the form adapted to the adjunction bijection). -/
@[reassoc]
lemma solKFactors_inv_naturality {K K' : Cpx} (f : K ⟶ K') :
    (solKFactors K).inv ≫ qs.map (solC.map f) = solK.map (qc.map f) ≫ (solKFactors K').inv :=
  solKFactorsIso.inv.naturality f

/-- Naturality of `incKFactors`. -/
@[reassoc]
lemma incKFactors_naturality {K K' : SCpx} (f : K ⟶ K') :
    incK.map (qs.map f) ≫ (incKFactors K').hom = (incKFactors K).hom ≫ qc.map (incC.map f) :=
  incKFactorsIso.hom.naturality f

/-- The adjunction bijection `Hom_K(solK X, Y) ≃ Hom_K(X, incK Y)`. -/
noncomputable def homEquivK (X : KCat) (Y : SKCat) :
    (solK.obj X ⟶ Y) ≃ (X ⟶ incK.obj Y) :=
  solKAdj.homEquiv X Y

/-- The adjunction bijection at the level of complexes of solid objects:
`Hom_K(solC K, N) ≃ Hom_K(K, incC N)`. -/
noncomputable def homKEquiv (K : Cpx) (N : SCpx) :
    (hs (solC.obj K) ⟶ hs N) ≃ (hq K ⟶ hq (incC.obj N)) :=
  ((solKFactors K).homCongr (Iso.refl (hs N))).trans
    ((homEquivK (hq K) (hs N)).trans
      ((Iso.refl (hq K)).homCongr (incKFactors N).symm))

/-- Naturality of `homKEquiv` in the first variable. -/
lemma homKEquiv_naturality {K K' : Cpx} (f : K ⟶ K') (N : SCpx)
    (v : hs (solC.obj K') ⟶ hs N) :
    homKEquiv K N (qs.map (solC.map f) ≫ v) = qc.map f ≫ homKEquiv K' N v := by
  simp only [homKEquiv, Equiv.trans_apply, Iso.homCongr_apply, homEquivK]
  simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id]
  rw [solKFactors_inv_naturality_assoc, Adjunction.homEquiv_naturality_left, Category.assoc]

/-- `incC` preserves and reflects quasi-isomorphisms. -/
lemma quasiIso_incC_map_iff {K K' : SCpx} (f : K ⟶ K') :
    QuasiIso (incC.map f) ↔ QuasiIso f :=
  HomologicalComplex.quasiIso_map_iff_of_preservesHomology f isSolid.ι

end Work.DERFORMAL
