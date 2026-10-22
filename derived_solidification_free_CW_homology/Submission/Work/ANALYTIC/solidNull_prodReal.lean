import Mathlib
import Submission.Work.ANALYTIC.RealSide
import Submission.Work.ANALYTIC.NullFamily
import Submission.Work.ANALYTIC.Main
import Submission.Work.ANALYTIC.preSolid_all
import Submission.Work.ANALYTIC.exists_realNullSeq
import Submission.Work.ANALYTIC.realActionPresheaf
import Submission.Work.FLAT.Main
import Submission.Work.FLAT.SheafifyTensor

/-!
# `∏_ℕ ℝ` is solid-null

The light condensed abelian group `∏_ℕ ℝ` (`S ↦ ℕ → C(S,ℝ)`, `Work.ANALYTIC.prodReal`) is a
module object over the light condensed ring `ℝ` (`S ↦ C(S,ℝ)`, `Work.ANALYTIC.realCond`) for the
coordinatewise multiplication.  By RC Thm 3.2.4(4) (formalised as
`Work.ANALYTIC.solidNull_of_realModule`) every unital `ℝ`-module object is solid-null, so
`∏_ℕ ℝ` is solid-null.

The module structure is built from the sectionwise multiplication
`Work.ANALYTIC.realMulPre` (`Submission/Work/ANALYTIC/realActionPresheaf.lean`) and the strong
monoidality of sheafification `L = Work.FLAT.sheafify`: the action is the composite

`realCond ⊗ prodReal ≅ L(A) ⊗ L(M) --L(unit) ⊗ L(χ)--> L(A) ⊗ L(M) --μ--> L(A ⊗ M)`
`--L(mul)--> L(M) ≅ prodReal`,

where `A = presheafOf realCond`, `M = presheafOf prodReal` and `χ` is the comparison isomorphism
`Z ≅ L(presheafOf Z)` (the inverse of the sheafification counit).  The unit law
`(u ▷ prodReal) ≫ act = (λ_ prodReal).hom` follows from the sectionwise unit law
`(unitPre ▷ M) ≫ mulPre = (λ_ M).hom` and the unitality axiom of the lax monoidal functor `L`.
-/

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- **Interchange of two whiskerings** in an arbitrary monoidal category: the two ways of
composing `f ▷ Z` with `Y ◁ g` agree.  (This is `MonoidalCategory.tensorHom_def` for the two
orders of the two whiskerings.) -/
lemma whisker_exchange {C : Type*} [Category C] [MonoidalCategory C]
    {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    (f ▷ Z) ≫ (Y ◁ g) = (X ◁ g) ≫ (f ▷ W) := by
  calc (f ▷ Z) ≫ (Y ◁ g)
      = (f ⊗ₘ 𝟙 Z) ≫ (𝟙 Y ⊗ₘ g) := by
        rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
    _ = f ⊗ₘ g := by
        rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    _ = (𝟙 X ⊗ₘ g) ≫ (f ⊗ₘ 𝟙 W) := by
        rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    _ = (X ◁ g) ≫ (f ▷ W) := by
        rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]

attribute [reassoc] whisker_exchange

/-- The action of `realCond ⊗ prodReal` on `prodReal`, obtained from the sectionwise
multiplication `realMulPre` by sheafification. -/
noncomputable def realCondAct : realCond ⊗ prodReal ⟶ prodReal :=
  ((Work.FLAT.sheafifyCounitIso realCond).hom ▷ prodReal) ≫
    (Work.FLAT.sheafify.obj realPresheaf' ◁ (Work.FLAT.sheafifyCounitIso prodReal).hom) ≫
    (Functor.Monoidal.μIso Work.FLAT.sheafify realPresheaf' prodRealPresheaf').hom ≫
    Work.FLAT.sheafify.map realMulPre ≫ (Work.FLAT.sheafifyCounitIso prodReal).inv

/-- The unit `ℤ ⟶ ℝ` of the light condensed ring `ℝ` (the constant function `1`), obtained from
the sectionwise unit `realUnitPre` by sheafification. -/
noncomputable def realCondUnit : 𝟙_ LightCondAb ⟶ realCond :=
  (Functor.Monoidal.εIso Work.FLAT.sheafify).hom ≫
    Work.FLAT.sheafify.map realUnitPre ≫ (Work.FLAT.sheafifyCounitIso realCond).inv

/-- **The unit law** for the sheafified action: `realCondUnit` is a unit for `realCondAct` on
`prodReal`.  This is the unitality axiom of the lax monoidal functor `sheafify`, applied to the
sectionwise unit law `Work.ANALYTIC.realUnitPre_mulPre`, together with the naturality of the left
unitor. -/
theorem realCondUnit_act :
    (realCondUnit ▷ prodReal) ≫ realCondAct = (λ_ prodReal).hom := by
  rw [realCondUnit, realCondAct]
  -- distribute the whiskering over the composite and cancel the `realCond ≅ L A` factor
  rw [comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  simp only [← comp_whiskerRight_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]
  -- the two interchanges, to bring `ε` and `L(unit)` next to `μ`
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc]
  rw [whisker_exchange_assoc]
  rw [Functor.Monoidal.μIso_hom, Functor.Monoidal.εIso_hom]
  -- naturality of `μ`
  rw [Functor.LaxMonoidal.μ_natural_left_assoc FLAT.sheafify realUnitPre prodRealPresheaf']
  -- the sectionwise unit law, under `sheafify`
  rw [← Functor.map_comp_assoc]
  rw [realUnitPre_mulPre]
  -- the unitality axiom of the lax monoidal functor `sheafify`
  rw [← Functor.LaxMonoidal.left_unitality_assoc]
  -- naturality of the left unitor, and `prodReal ≅ L M`
  rw [leftUnitor_naturality_assoc]
  rw [Iso.hom_inv_id, Category.comp_id]

theorem solidNull_prodReal [CategoryTheory.Limits.PreservesFiniteLimits (CategoryTheory.MonoidalCategory.tensorLeft LightCondensed.P)] : Work.ANALYTIC.SolidNull ((DerivedCategory.singleFunctor LightCondAb 0).obj Work.ANALYTIC.prodReal) :=
  solidNull_of_realModule prodReal realCondAct realCondUnit realCondUnit_act
    (exists_realNullSeq realCondUnit) (preSolid_all prodReal)

end

end Work.ANALYTIC
