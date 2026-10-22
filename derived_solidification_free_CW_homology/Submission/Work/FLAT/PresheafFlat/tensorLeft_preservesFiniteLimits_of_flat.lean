import Mathlib
import Submission.Work.FLAT.Setup

/-!
# AREA FLAT — the *sectionwise* tensor product with a sectionwise flat presheaf is left exact

`PreMod = (LightProfinite.{0})ᵒᵖ ⥤ ModuleCat.{0} ℤ` carries the pointwise (Day) monoidal
structure of `CategoryTheory.Monoidal.FunctorCategory.functorCategoryMonoidal`, whose tensor
product and whiskering are computed *sectionwise*:

* `(F ⊗ G).obj S = F.obj S ⊗ G.obj S`  (`Monoidal.FunctorCategory.tensorObj_obj`),
* `(F ◁ β).app S = F.obj S ◁ β.app S`  (`Monoidal.FunctorCategory.whiskerLeft_app`).

Consequently `tensorLeft F`, evaluated at the section `S`, *is* the functor
`tensorLeft (F.obj S)` on `ModuleCat ℤ`.  Since limits in a functor category are computed
pointwise (`evaluation S` preserves all limits), a functor out of `PreMod` preserves finite
limits as soon as each of its composites with the evaluations `evaluation S` does.  This turns
the statement into the classical theorem that tensoring with a flat module is left exact
(`Module.Flat.iff_preservesFiniteLimits_tensorLeft`).

This is exactly the hypothesis consumed by
`Work.FLAT.preservesFiniteLimits_tensorLeft_sheafify` (`SheafifyTensor.lean`), applied to the
sectionwise free presheaf `sectionwiseFree T` (`Work.FLAT.sectionwiseFree_flat`).
-/

namespace Work.FLAT.PresheafFlat

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

/-- Tensoring (on the left) with a flat `ℤ`-module, viewed as the functor `tensorLeft M` on
`ModuleCat ℤ`, preserves finite limits. -/
lemma preservesFiniteLimits_tensorLeft_of_flat (M : ModuleCat.{0} ℤ) (hM : Module.Flat ℤ M) :
    PreservesFiniteLimits (tensorLeft M) :=
  (Module.Flat.iff_preservesFiniteLimits_tensorLeft M).1 hM

/-- **The sectionwise tensor product with a sectionwise flat presheaf is left exact.**  If the
presheaf `F` of abelian groups on light profinite sets has flat sections `F.obj S`, then the
endofunctor `tensorLeft F = (F ⊗ -)` of `PreMod` preserves finite limits.

(It is the sectionwise tensor product, so this is the pointwise flatness statement; the
sheafification step is handled separately in `Work.FLAT.preservesFiniteLimits_tensorLeft_sheafify`.) -/
theorem tensorLeft_preservesFiniteLimits_of_flat (F : Work.FLAT.PreMod)
    (hF : ∀ S, Module.Flat ℤ (F.obj S)) :
    CategoryTheory.Limits.PreservesFiniteLimits
      (CategoryTheory.MonoidalCategory.tensorLeft F) := by
  -- It suffices to test the composites with the pointwise evaluations at each section.
  apply preservesFiniteLimits_of_evaluation
  intro S
  -- At a section, `tensorLeft F` *is* `tensorLeft (F.obj S)` (`tensorObj_obj`, `whiskerLeft_app`).
  change PreservesFiniteLimits
    ((evaluation (LightProfinite.{0})ᵒᵖ (ModuleCat.{0} ℤ)).obj S ⋙ tensorLeft (F.obj S))
  have hS : Module.Flat ℤ (F.obj S) := hF S
  -- `evaluation S` preserves all limits, and `tensorLeft (F.obj S)` is left exact by flatness.
  have hfin : PreservesFiniteLimits (tensorLeft (F.obj S)) :=
    preservesFiniteLimits_tensorLeft_of_flat (F.obj S) hS
  infer_instance

end Work.FLAT.PresheafFlat
