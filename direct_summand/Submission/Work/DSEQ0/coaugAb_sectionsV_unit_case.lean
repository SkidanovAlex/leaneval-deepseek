import Mathlib
import Submission.Work.DSEQ0.AugAbSetup
import Submission.Work.DSEQ0.homotopy_zeroAb
import Submission.Work.DSF1.Sheaf.cechTrivAll_local

/-!
# The augmented Čech complex over an open contained in a member of the cover

Let `X` be a scheme, `U : ι → X.Opens` a family of opens, `V : X.Opens` an open contained in
one member `U i₀` of the family, and let

`Q := C.cechShPresheaf X ⋙ sectionsV X V`,

the presheaf of abelian groups `Q(W) = Γ(W ⊓ V, 𝒪_X)`.  This module proves
`Work.DSEQ0.coaugAb_sectionsV_unit_case`: the coaugmentation

`coaugAb X U Q : Q(⊤) ⟶ Č⁰(U; Q)`

is injective and its image is exactly the group of `0`-cocycles of the Čech complex of `U`
with coefficients `Q` — i.e. the augmentation `Q(⊤) ⟶ Č•(U; Q)` is exact in the first two
degrees.  Equivalently, the augmented complex `0 ⟶ Q(⊤) ⟶ Č⁰ ⟶ Č¹ ⟶ ⋯` has `H⁰ = Q(⊤)`
and vanishes in degree `-1`.

## The argument

The family `{U i ⊓ V}` of opens of `V` contains the member `V` itself (`U i₀ ⊓ V = V`), so the
Čech complex of `U` with coefficients `Q` is contractible in the augmented sense: inserting the
index `i₀` at position `0` of a simplex does not change the open `Eobj U n x ⊓ V`, so the coface
maps inserting `i₀` are inverted by `Q`
(`Work.DSEQ0.isIsoDelAbTop_sectionsV`, from the general restriction lemma
`Work.DSEQ0.isIso_sectionsVMap`).  With

* `kAb U Q h.2` the contracting homotopy of the unaugmented complex
  (`Submission/Work/DSF1/Sheaf/cechTrivAll_local.lean`),
* `kTopAb U Q h : Č⁰ ⟶ Q(⊤)` the contraction of the coaugmentation
  (`Work.DSEQ0.kTopAb`, with `coaugAb ≫ kTopAb = 𝟙`),

the two chain-homotopy identities give the result:

* `coaugAb ≫ kTopAb = 𝟙` (`Work.DSEQ0.coaugAb_comp_kTopAb`) says that `coaugAb` is a split
  monomorphism, hence injective;
* `kTopAb ≫ coaugAb + d 0 1 ≫ kAb 0 = 𝟙` (`Work.DSEQ0.homotopy_zeroAb`, proved in
  `Submission/Work/DSEQ0/homotopy_zeroAb.lean`) says that for a `0`-cocycle `z` one has
  `coaugAb (kTopAb z) = z`.

The coaugmentation and the two homotopy identities are the `AddCommGrpCat`-valued companion of
`Work.DSF1.Cech.UnitCase` (which is for coefficients a presheaf of `S`-modules).  This is the
"`H⁰`" statement used by the area `DSEQ0`'s quasi-isomorphism `Work.DSEQ0.quasiIso_augZ`.
-/

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

set_option backward.isDefEq.respectTransparency false

variable {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}

/-- **The unit case, for coefficients a presheaf of abelian groups.**  If a presheaf `Q` of
abelian groups inverts the coface maps of the Čech nerve which insert `i₀`, and also the
restriction `Q(⊤) ⟶ Q (U i₀)` (`Work.DSEQ0.IsIsoDelAbTop`), then the coaugmentation of the
Čech complex of the family `U` with coefficients `Q` is injective with image the
`0`-cocycles. -/
theorem coaugAb_injective_and_ker (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u})
    {i₀ : ι} (h : IsIsoDelAbTop U Q i₀) :
    Function.Injective (ConcreteCategory.hom (coaugAb X U Q)) ∧
      (∀ z : ((cechComplexFunctor U).obj Q).X 0,
        ((cechComplexFunctor U).obj Q).d 0 1 z = 0 →
        ∃ s : Q.obj (op ⊤), coaugAb X U Q s = z) := by
  refine ⟨?_, ?_⟩
  · -- `kTopAb` is a left inverse of `coaugAb`, so `coaugAb` is injective.
    have hK : Function.LeftInverse (ConcreteCategory.hom (kTopAb U Q h))
        (ConcreteCategory.hom (coaugAb X U Q)) := by
      intro x
      have hc := congrArg (fun f : Q.obj (op ⊤) ⟶ Q.obj (op ⊤) =>
        (ConcreteCategory.hom f) x) (coaugAb_comp_kTopAb U Q h)
      simpa only [AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply] using hc
    exact hK.injective
  · -- The chain-homotopy identity in degree `0`.
    intro z hz
    refine ⟨(ConcreteCategory.hom (kTopAb U Q h)) z, ?_⟩
    have hh := congrArg (fun f : ((cechComplexFunctor U).obj Q).X 0 ⟶
        ((cechComplexFunctor U).obj Q).X 0 => (ConcreteCategory.hom f) z)
      (homotopy_zeroAb U Q h)
    simp only [AddCommGrpCat.hom_add_apply, AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply,
      hz, map_zero, add_zero] at hh
    exact hh

/-- **The coaugmentation of the Čech complex with coefficients `Γ(− ⊓ V, 𝒪_X)` is injective with
image exactly the `0`-cocycles, when `V` is contained in a member of the family.** -/
theorem coaugAb_sectionsV_unit_case (X : AlgebraicGeometry.Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) (V : X.Opens) (i₀ : ι) (hV : V ≤ U i₀) :
    Function.Injective (CategoryTheory.ConcreteCategory.hom (Work.DSEQ0.coaugAb X U
        (CategoryTheory.Functor.comp (Work.DSEQ0.C.cechShPresheaf X)
          (Work.DSEQ0.sectionsV X V)))) ∧
      (∀ z : ((CategoryTheory.cechComplexFunctor U).obj
          (CategoryTheory.Functor.comp (Work.DSEQ0.C.cechShPresheaf X)
            (Work.DSEQ0.sectionsV X V))).X 0,
        ((CategoryTheory.cechComplexFunctor U).obj
          (CategoryTheory.Functor.comp (Work.DSEQ0.C.cechShPresheaf X)
            (Work.DSEQ0.sectionsV X V))).d 0 1 z = 0 →
        ∃ s : (CategoryTheory.Functor.comp (Work.DSEQ0.C.cechShPresheaf X)
            (Work.DSEQ0.sectionsV X V)).obj (Opposite.op ⊤),
          Work.DSEQ0.coaugAb X U (CategoryTheory.Functor.comp (Work.DSEQ0.C.cechShPresheaf X)
            (Work.DSEQ0.sectionsV X V)) s = z) :=
  coaugAb_injective_and_ker U (C.cechShPresheaf X ⋙ sectionsV X V)
    (isIsoDelAbTop_sectionsV X U V i₀ hV)

end Work.DSEQ0
