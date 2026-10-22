import Mathlib
import Submission.Work.ANALYTIC.RealSideDefs
import Submission.Work.ANALYTIC.BoundedRealType
import Submission.Work.ANALYTIC.boundedReal_coprod
import Submission.Work.ANALYTIC.boundedSeq_sheaf

/-!
# `∏^bnd ℝ` preserves finite products

`Work.ANALYTIC.boundedRealPresheaf` (`Submission/Work/ANALYTIC/RealSideDefs.lean`) is the presheaf
`S ↦ {x : ℕ → C(S,ℝ) | ∃ N : ℝ, ∀ n s, |x n s| ≤ N}` of uniformly bounded families of continuous
real-valued functions — the `ℝ`-valued analogue of the presheaf `∏^bnd ℤ`, and half of the
`ℝ`-side (AN2 of `Submission/Work/ANALYTIC/README.md`) of the null-sequence machinery.

This file proves that, as a functor to `Type` (i.e. after `forget (ModuleCat ℤ)`), it preserves
finite products, which is the first half of the statement that `∏^bnd ℝ` is a sheaf on the
coherent (resp. regular) topology of `LightProfinite`.  The second half is
`Work.ANALYTIC.boundedReal_equalizerCondition`.

The mathematical content is exactly that of the `ℤ`-valued statement proved in
`Submission/Work/ANALYTIC/boundedSeq_sheaf.lean` and we follow the same route:

* finite products in `LightProfiniteᵒᵖ` are finite coproducts in `LightProfinite`, i.e. disjoint
  unions; a uniformly bounded family on a disjoint union is the same thing as a family of
  uniformly bounded families on the summands (a bound on a finite disjoint union is the sum over
  the finitely many summand bounds, which is where *finiteness* of the index set is used);
* this is the concrete bijection `Work.ANALYTIC.boundedReal_coprod`
  (`Submission/Work/ANALYTIC/boundedReal_coprod.lean`), which identifies the comparison map
  `boundedRealTypePresheaf (∐ X) ⟶ ∏ᶜ boundedRealTypePresheaf (X a)` with the `Pi.lift` of the
  restrictions along the canonical coproduct inclusions;
* `isIso_piLift_iff` (from `Submission/Work/ANALYTIC/boundedSeq_sheaf.lean`) turns that bijection
  into `IsIso` of the `Pi.lift`, and hence into `IsIso` of the comparison map of the *canonical*
  coproduct, using `opCoproductIsoProduct'` to compare the explicit finite coproduct with the
  canonical one.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open Opposite

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid
open CategoryTheory.regularTopology

universe u

/-- For a finite family `X` of light profinite sets, the canonical comparison map
`boundedRealTypePresheaf (∐ X) ⟶ ∏ᶜ boundedRealTypePresheaf (X a)` (with respect to the
*canonical* coproduct in `LightProfinite`) is an isomorphism.

The proof compares it with the comparison map of the *explicit* finite coproduct
(`CompHausLike.finiteCoproduct`), where the statement is the concrete `boundedReal_coprod`; the two
are related by `opCoproductIsoProduct'`. -/
theorem boundedRealType_piComparison_isIso {α : Type} [Finite α] (X : α → LightProfinite.{u}) :
    IsIso (piComparison boundedRealTypePresheaf.{u} (fun a => op (X a))) := by
  have hc : IsColimit (CompHausLike.finiteCoproduct.cofan X) :=
    CompHausLike.finiteCoproduct.isColimit X
  have hf : IsLimit (Fan.mk (∏ᶜ fun a => op (X a)) (Pi.π (fun a => op (X a)))) :=
    productIsProduct (fun a => op (X a))
  let hφ : op (CompHausLike.finiteCoproduct X) ≅ ∏ᶜ (fun a => op (X a)) :=
    opCoproductIsoProduct' hc hf
  have hstep (a : α) :
      hφ.inv ≫ (CompHausLike.finiteCoproduct.ι X a).op = Pi.π (fun a => op (X a)) a :=
    opCoproductIsoProduct'_inv_comp_inj hc hf a
  have key : piComparison boundedRealTypePresheaf.{u} (fun a => op (X a)) =
      boundedRealTypePresheaf.{u}.map hφ.inv ≫
        Pi.lift (fun a => boundedRealTypePresheaf.{u}.map
          (CompHausLike.finiteCoproduct.ι X a).op) := by
    refine Pi.hom_ext _ _ (fun a => ?_)
    rw [Category.assoc, Pi.lift_comp_π, piComparison_comp_π,
      ← boundedRealTypePresheaf.{u}.map_comp, hstep a]
  rw [key]
  haveI h1 : IsIso
      (Pi.lift (fun a => boundedRealTypePresheaf.{u}.map
        (CompHausLike.finiteCoproduct.ι X a).op)) :=
    (isIso_piLift_iff (fun a => boundedRealTypePresheaf.{u}.obj (op (X a)))
      (fun a => boundedRealTypePresheaf.{u}.map
        (CompHausLike.finiteCoproduct.ι X a).op)).mpr
      (boundedReal_coprod X)
  haveI h2 : IsIso (boundedRealTypePresheaf.{u}.map hφ.inv) :=
    Functor.map_isIso boundedRealTypePresheaf.{u} hφ.inv
  exact IsIso.comp_isIso

/-- `boundedRealTypePresheaf` preserves the limit of a finite discrete diagram. -/
theorem boundedRealType_preservesLimit_discrete {α : Type} [Finite α]
    (X : α → LightProfinite.{u}) :
    PreservesLimit (Discrete.functor (fun a => op (X a))) boundedRealTypePresheaf.{u} :=
  @PreservesProduct.of_iso_comparison _ _ _ _ boundedRealTypePresheaf.{u} _ (fun a => op (X a)) _ _
    (boundedRealType_piComparison_isIso X)

/-- The presheaf of uniformly bounded families of continuous `ℝ`-valued functions preserves finite
products.  Every finite discrete limit in `LightProfiniteᵒᵖ` is, up to a discrete iso of diagrams,
the canonical product of a finite family of light profinite sets, and the comparison map is an
isomorphism by `boundedRealType_piComparison_isIso`. -/
theorem boundedRealType_preservesFiniteProducts :
    PreservesFiniteProducts boundedRealTypePresheaf.{u} where
  preserves n := by
    refine { preservesLimit := fun {K} => ?_ }
    haveI : PreservesLimit (Discrete.functor fun j => op (unop (K.obj (Discrete.mk j))))
        boundedRealTypePresheaf.{u} :=
      boundedRealType_preservesLimit_discrete _
    let i : K ≅ Discrete.functor (fun j => op (unop (K.obj (Discrete.mk j)))) :=
      Discrete.natIsoFunctor
    exact preservesLimit_of_iso_diagram boundedRealTypePresheaf.{u} i.symm

/-- The presheaf `∏^bnd ℝ` of uniformly bounded families of continuous real-valued functions
(`Work.ANALYTIC.boundedRealPresheaf`), viewed as a presheaf of types via
`forget (ModuleCat ℤ)`, preserves finite products.

Proof: `boundedRealTypePresheaf` is by definition `boundedRealPresheaf ⋙ forget (ModuleCat ℤ)`
(`Submission/Work/ANALYTIC/BoundedRealType.lean`), and the statement for it is
`boundedRealType_preservesFiniteProducts` above. -/
theorem boundedReal_preservesFiniteProducts : CategoryTheory.Limits.PreservesFiniteProducts (CategoryTheory.Functor.comp Work.ANALYTIC.boundedRealPresheaf (CategoryTheory.forget (ModuleCat ℤ))) := boundedRealType_preservesFiniteProducts

end Work.ANALYTIC
