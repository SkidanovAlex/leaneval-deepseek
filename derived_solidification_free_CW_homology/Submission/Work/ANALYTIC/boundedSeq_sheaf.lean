import Mathlib
import Submission.Work.ANALYTIC.Bounded
import Submission.Work.ANALYTIC.BoundedType
import Submission.Work.ANALYTIC.boundedSeq_coprod
import Submission.Work.ANALYTIC.boundedSeq_map_injective
import Submission.Work.ANALYTIC.boundedSeq_descend
import Submission.Work.ANALYTIC.boundedSeq_pullback_compat

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open CategoryTheory.regularTopology

noncomputable section

namespace Work.ANALYTIC

open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

universe u

/-!
# The sheaf of uniformly bounded sequences

The presheaf `boundedTypePresheaf` of `Submission/Work/ANALYTIC/BoundedType.lean` (the underlying
presheaf of types of `boundedPresheaf`: `S ↦ boundedSeqSet S`, uniformly bounded families of
continuous `ℤ`-valued functions) is a sheaf for the coherent topology on `LightProfinite`: it
preserves finite products and satisfies the equalizer condition.

The pieces proved elsewhere and used here are

* `boundedSeq_coprod` — for a finite family `X` the restrictions to the summands identify the value
  at the explicit finite coproduct with the product of the values (this is where finiteness of the
  index set is used: the individual bounds are combined into one);
* `boundedSeq_map_injective` — pullback along a surjection is injective (the separatedness half);
* `boundedSeq_pullback_compat` — the compatibility on the kernel pair, in pointwise form;
* `boundedSeq_descend` — the descent of a bounded family along a surjection (continuity of the
  descended coordinates comes from `π` being a quotient map, compact source, Hausdorff target).

The step from the concrete bijectivity `boundedSeq_coprod` to the categorical `IsIso` of the
comparison map is `isIso_piLift_iff` below.
-/

/-- In `Type`, the canonical map `Pi.lift g : X ⟶ ∏ᶜ F` is an isomorphism iff the corresponding
"dependent function" map `x ↦ (j ↦ g j x)` is a bijection.  This is the bridge between the concrete
statement `boundedSeq_coprod` and the categorical comparison map `piComparison`. -/
theorem isIso_piLift_iff {J : Type} {X : Type u} (F : J → Type u) (g : (j : J) → X ⟶ F j) :
    IsIso (Pi.lift g) ↔ Function.Bijective (fun x : X => fun j : J => g j x) := by
  have hL : ⇑(Types.productIso F).hom ∘ ⇑(Pi.lift g) =
      (fun x : X => fun j : J => g j x) := by
    funext x j
    simp only [Function.comp_apply]
    rw [Types.productIso_hom_comp_eval_apply]
    exact ConcreteCategory.congr_hom (Pi.lift_comp_π g j) x
  have hbijhom : Function.Bijective ⇑(Types.productIso F).hom :=
    (isIso_iff_bijective _).mp inferInstance
  constructor
  · intro hI
    have hcomp := hbijhom.comp ((isIso_iff_bijective (Pi.lift g)).mp hI)
    rw [hL] at hcomp
    exact hcomp
  · intro hb
    refine (isIso_iff_bijective (Pi.lift g)).mpr ?_
    refine Function.Bijective.of_comp_left ?_ hbijhom.injective
    rw [hL]
    exact hb

/-- For a finite family `X` of light profinite sets, the canonical comparison map
`boundedTypePresheaf (∐ X) ⟶ ∏ᶜ boundedTypePresheaf (X a)` (with respect to the *canonical*
coproduct in `LightProfinite`) is an isomorphism.

The proof compares it with the comparison map of the *explicit* finite coproduct
(`CompHausLike.finiteCoproduct`), where the statement is the concrete `boundedSeq_coprod`; the two
are related by `opCoproductIsoProduct'`. -/
theorem boundedSeq_piComparison_isIso {α : Type} [Finite α] (X : α → LightProfinite.{u}) :
    IsIso (piComparison boundedTypePresheaf.{u} (fun a => op (X a))) := by
  have hc : IsColimit (CompHausLike.finiteCoproduct.cofan X) :=
    CompHausLike.finiteCoproduct.isColimit X
  have hf : IsLimit (Fan.mk (∏ᶜ fun a => op (X a)) (Pi.π (fun a => op (X a)))) :=
    productIsProduct (fun a => op (X a))
  let hφ : op (CompHausLike.finiteCoproduct X) ≅ ∏ᶜ (fun a => op (X a)) :=
    opCoproductIsoProduct' hc hf
  have hstep (a : α) :
      hφ.inv ≫ (CompHausLike.finiteCoproduct.ι X a).op = Pi.π (fun a => op (X a)) a :=
    opCoproductIsoProduct'_inv_comp_inj hc hf a
  have key : piComparison boundedTypePresheaf (fun a => op (X a)) =
      boundedTypePresheaf.map hφ.inv ≫
        Pi.lift (fun a => boundedTypePresheaf.map (CompHausLike.finiteCoproduct.ι X a).op) := by
    refine Pi.hom_ext _ _ (fun a => ?_)
    rw [Category.assoc, Pi.lift_comp_π, piComparison_comp_π, ← boundedTypePresheaf.map_comp,
      hstep a]
  rw [key]
  haveI h1 : IsIso
      (Pi.lift (fun a => boundedTypePresheaf.map (CompHausLike.finiteCoproduct.ι X a).op)) :=
    (isIso_piLift_iff (fun a => boundedTypePresheaf.obj (op (X a)))
      (fun a => boundedTypePresheaf.map (CompHausLike.finiteCoproduct.ι X a).op)).mpr
      (boundedSeq_coprod X)
  haveI h2 : IsIso (boundedTypePresheaf.map hφ.inv) :=
    Functor.map_isIso boundedTypePresheaf hφ.inv
  exact IsIso.comp_isIso

/-- `boundedTypePresheaf` preserves the limit of a finite discrete diagram. -/
theorem boundedSeq_preservesLimit_discrete {α : Type} [Finite α] (X : α → LightProfinite.{u}) :
    PreservesLimit (Discrete.functor (fun a => op (X a))) boundedTypePresheaf.{u} :=
  @PreservesProduct.of_iso_comparison _ _ _ _ boundedTypePresheaf _ (fun a => op (X a)) _ _
    (boundedSeq_piComparison_isIso X)

/-- **First half of the sheaf condition**: the presheaf of uniformly bounded sequences preserves
finite products.  Every finite discrete limit in `LightProfiniteᵒᵖ` is, up to a discrete iso of
diagrams, the canonical product of a finite family of light profinite sets, and the comparison map
is an isomorphism by `boundedSeq_piComparison_isIso`. -/
theorem boundedSeq_preservesFiniteProducts : PreservesFiniteProducts boundedTypePresheaf.{u} where
  preserves n := by
    refine { preservesLimit := fun {K} => ?_ }
    haveI : PreservesLimit (Discrete.functor fun j => op (unop (K.obj (Discrete.mk j))))
        boundedTypePresheaf.{u} :=
      boundedSeq_preservesLimit_discrete _
    let i : K ≅ Discrete.functor (fun j => op (unop (K.obj (Discrete.mk j)))) :=
      Discrete.natIsoFunctor
    exact preservesLimit_of_iso_diagram boundedTypePresheaf.{u} i.symm

/-- **Second half of the sheaf condition**: the presheaf of uniformly bounded sequences satisfies
the equalizer condition for effective epimorphisms, i.e. for surjective maps of light profinite
sets (these are compact Hausdorff spaces, so `π` is a quotient map and the descended coordinates
are continuous). -/
theorem boundedSeq_equalizerCondition : EqualizerCondition boundedTypePresheaf.{u} := by
  refine EqualizerCondition.mk boundedTypePresheaf.{u} (fun X B π _ _ => ?_)
  constructor
  · intro a b h
    refine boundedSeq_map_injective π (fun y => ?_) a b (congrArg Subtype.val h)
    exact (LightProfinite.effectiveEpi_iff_surjective π).mp inferInstance y
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := boundedSeq_descend π
      (fun y => (LightProfinite.effectiveEpi_iff_surjective π).mp inferInstance y) a
      (boundedSeq_pullback_compat π a ha)
    refine ⟨b, ?_⟩
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    funext n
    exact ContinuousMap.ext (fun x => hb n x)

/-- The presheaf of uniformly bounded sequences (`Submission/Work/ANALYTIC/Bounded.lean`) is a sheaf
for the coherent topology on `LightProfinite`: it preserves finite products and satisfies the
equalizer condition.  Consequently `LightCondensed.ofSheafForgetLightProfinite boundedPresheaf _` is
the light condensed abelian group `∏^bnd ℤ` of REFS/03 §2, whose `S`-points are the uniformly
bounded families of continuous `ℤ`-valued functions on `S` (definitionally).

Route: for a finite coproduct `S ⊔ T` in `LightProfinite`, evaluation gives
`boundedSeqSet (S ⊔ T) ≅ boundedSeqSet S × boundedSeqSet T`, and `boundedSeqSet ∅` is a
subsingleton (terminal).  For the equalizer condition with an effective epimorphism `π : X ⟶ B`
(equivalently a surjection, `LightProfinite.effectiveEpi_iff_surjective`), use `EqualizerCondition.mk`
for Type-valued presheaves: injectivity of the comparison map is immediate, and for the lifting
property one shows that if a family over `B` pulls back to a bounded family over `X`, then it is
bounded over `B` with the same bound, because every point of `B` is the image of a point of `X`
(surjectivity).  Use `Topology.IsQuotientMap.of_surjective_continuous` for the continuity of the
descended coordinates. -/
theorem boundedSeq_sheaf :
    PreservesFiniteProducts (boundedPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) ∧
      EqualizerCondition (boundedPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) :=
  ⟨boundedSeq_preservesFiniteProducts, boundedSeq_equalizerCondition⟩

/-- **The light condensed abelian group `∏^bnd ℤ`** of REFS/03 §2, whose `S`-points are the
uniformly bounded families of continuous `ℤ`-valued functions on `S` (definitionally).  This is the
object `Bd` of `IsBoundedSeqSolidEquiv` (`Submission/Work/ANALYTIC/Basic.lean`). -/
noncomputable def boundedSeq : LightCondAb :=
  letI : PreservesFiniteProducts (boundedPresheaf ⋙ CategoryTheory.forget (ModuleCat ℤ)) :=
    boundedSeq_preservesFiniteProducts
  LightCondensed.ofSheafForgetLightProfinite boundedPresheaf boundedSeq_equalizerCondition

/-- The `S`-points of `boundedSeq` are the uniformly bounded families of continuous `ℤ`-valued
functions on `S` (definitionally). -/
theorem boundedSeq_obj_obj (S : LightProfinite) :
    ↥(boundedSeq.obj.obj (Opposite.op S)) = boundedSeqSet S := rfl

end Work.ANALYTIC
