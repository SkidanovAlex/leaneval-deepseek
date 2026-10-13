import Mathlib
import Submission.Work.DSEQ0.eulerCharDefs
import Submission.Work.DSEQ0.isIso_extendScalars_cechPresheaf_restrict
import Submission.Work.DSEQ0.isIso_extendScalars_map_piMap
import Submission.Work.DSF1.Sheaf.mapHomologicalComplex_extendUpNat
import Submission.Work.DSG4a.cech_d_comm_pi

/-!
# `cechZAway_iso_curry_ext`

The base change (along `A → A_g = Localization.Away g`) of the Čech complex `Č(U; 𝒪_X)` is
isomorphic to the base change of the Čech complex of the "curried" presheaf
`V ↦ Γ(X, W ⊓ V)`, where `W = f ⁻¹ᵁ D(g) = awayOpen A X f g`.

The comparison is the base change of the termwise restriction
`Γ(X, V) → Γ(X, W ⊓ V)`, which becomes an isomorphism after inverting `g` as soon as `V` is
affine: `Γ(X, W ⊓ V) = Γ(X, V)[1/g]` (this is
`Work.DSEQ0.isIso_extendScalars_cechPresheaf_restrict`, applied to the affine opens `⨅ U(y a)`
supplied by the hypothesis `hint`).  Base change `A_g ⊗_A -` commutes with the finite products
out of which the Čech complex is built (`Work.DSEQ0.isIso_extendScalars_map_piMap`), so the
comparison is an isomorphism of complexes in degree `≥ 0`, and the `ℤ`-indexed complexes are
obtained by extension by zero (`Work.DSF1.Sheaf.mapHomologicalComplex_extendUpNat`).
-/

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.power

/-- The endofunctor `V ↦ W ⊓ V` of `X.Opensᵒᵖ`, for a fixed open `W`. -/
noncomputable def awayCurryGG (X : AlgebraicGeometry.Scheme.{u}) (W : X.Opens) :
    X.Opensᵒᵖ ⥤ X.Opensᵒᵖ where
  obj V := Opposite.op (W ⊓ V.unop)
  map {V V'} f := (homOfLE (inf_le_inf_left W (leOfHom f.unop))).op
  map_id V := by ext <;> rfl
  map_comp f g := by ext <;> rfl

/-- The natural transformation `𝟭 ⟶ (V ↦ W ⊓ V)` given by `W ⊓ V ≤ V`. -/
noncomputable def awayCurryNu (X : AlgebraicGeometry.Scheme.{u}) (W : X.Opens) :
    𝟭 X.Opensᵒᵖ ⟶ awayCurryGG X W where
  app V := (homOfLE (inf_le_right : W ⊓ V.unop ≤ V.unop)).op
  naturality V V' i := by apply Subsingleton.elim

/-- The natural transformation `cechPresheaf A X f ⟶ curryPresheaf A X f W` given by the
restriction `Γ(X, V) → Γ(X, W ⊓ V)`. -/
noncomputable def awayCurryMu (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) (W : X.Opens) :
    DSMap.cechPresheaf A X f ⟶ Work.DSEQ0.curryPresheaf A X f W :=
  Functor.whiskerRight (awayCurryNu X W) (DSMap.cechPresheaf A X f)

/-- The Čech index `((mk U).cech.obj ⦋n⦌).obj x` of Mathlib's formal-coproduct machinery is the
intersection `⨅ a, U (x a)`. -/
lemma cechOb_eq_iInf {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (n : ℕ) (x : Work.DSG4a.cechIx U n) :
    Work.DSG4a.cechOb U n x = ⨅ a, U (x a) := by
  simp only [Work.DSG4a.cechOb, FormalCoproduct.cech_obj, FormalCoproduct.power]
  apply le_antisymm
  · exact le_iInf (fun a => (Pi.π (fun a => U (x a)) a).le)
  · exact (Pi.lift (fun a => homOfLE (iInf_le (fun a => U (x a)) a))).le

theorem cechZAway_iso_curry_ext (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (g : A) {W : X.Opens} (hW : W = Work.DSEQ0.awayOpen A X f g)
    (hint : ∀ (n : ℕ) (y : Fin (n + 1) → ι),
      AlgebraicGeometry.IsAffineOpen (⨅ a, U (y a))) :
    Nonempty (CategoryTheory.Iso (Work.DSEQ0.cechZAway A X f U g)
      ((CategoryTheory.Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away g)))
        (ComplexShape.up ℤ)).obj (Work.DSEQ0.curryComplexZ A X f W U))) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : DecidableEq ι := Classical.decEq ι
  haveI hfin : ∀ n : ℕ, Fintype (Work.DSG4a.cechIx U n) :=
    fun n => inferInstanceAs (Fintype (Fin (n + 1) → ι))
  haveI hdec : ∀ n : ℕ, DecidableEq (Work.DSG4a.cechIx U n) :=
    fun n => inferInstanceAs (DecidableEq (Fin (n + 1) → ι))
  let E : ModuleCat.{u} A ⥤ ModuleCat.{u} (Localization.Away g) :=
    ModuleCat.extendScalars (algebraMap A (Localization.Away g))
  haveI hEadd : E.Additive := Work.DSG4a.extendScalarsAdditivePi _
  let F : X.Opensᵒᵖ ⥤ ModuleCat.{u} A := DSMap.cechPresheaf A X f
  let Fw : X.Opensᵒᵖ ⥤ ModuleCat.{u} A := Work.DSEQ0.curryPresheaf A X f W
  let P : CochainComplex (ModuleCat.{u} A) ℕ := (CategoryTheory.cechComplexFunctor U).obj F
  let Q : CochainComplex (ModuleCat.{u} A) ℕ := (CategoryTheory.cechComplexFunctor U).obj Fw
  let ψ : P ⟶ Q := (CategoryTheory.cechComplexFunctor U).map (awayCurryMu A X f W)
  -- Degreewise description of the comparison.
  have hpsif : ∀ n : ℕ, ψ.f n = CategoryTheory.Limits.Pi.map
      (fun x => (awayCurryMu A X f W).app (Opposite.op (Work.DSG4a.cechOb U n x))) := by
    intro n
    simp only [ψ, CategoryTheory.cechComplexFunctor,
      FormalCoproduct.cochainComplexFunctor_map_f]
    congr 1
  -- Each component of the base-changed comparison is an isomorphism.
  have hcomp : ∀ n : ℕ,
      IsIso (((E.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ).f n) := by
    intro n
    rw [Functor.mapHomologicalComplex_map_f, hpsif n]
    refine isIso_extendScalars_map_piMap (algebraMap A (Localization.Away g))
      (fun x => F.obj (Opposite.op (Work.DSG4a.cechOb U n x)))
      (fun x => Fw.obj (Opposite.op (Work.DSG4a.cechOb U n x)))
      (fun x => (awayCurryMu A X f W).app (Opposite.op (Work.DSG4a.cechOb U n x)))
      (fun x => ?_)
    have haff : IsAffineOpen (Work.DSG4a.cechOb U n x) := by
      rw [cechOb_eq_iInf U n x]; exact hint n x
    have hx := isIso_extendScalars_cechPresheaf_restrict A X f g
      (Work.DSG4a.cechOb U n x) haff
    show IsIso (E.map ((awayCurryMu A X f W).app (Opposite.op (Work.DSG4a.cechOb U n x))))
    rw [hW]
    rw [show (awayCurryMu A X f (Work.DSEQ0.awayOpen A X f g)).app
          (Opposite.op (Work.DSG4a.cechOb U n x))
        = F.map (homOfLE (inf_le_right :
            Work.DSEQ0.awayOpen A X f g ⊓ Work.DSG4a.cechOb U n x ≤
              Work.DSG4a.cechOb U n x)).op from rfl]
    exact hx
  haveI : ∀ n : ℕ,
      IsIso (((E.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ).f n) := hcomp
  haveI : IsIso ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ) :=
    HomologicalComplex.Hom.isIso_of_components _
  let eψ : (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj P ≅
      (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj Q :=
    asIso ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map ψ)
  refine ⟨?_⟩
  exact (Work.DSF1.Sheaf.mapHomologicalComplex_extendUpNat E P).some ≪≫
    ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} (Localization.Away g))).mapIso eψ) ≪≫
    (Work.DSF1.Sheaf.mapHomologicalComplex_extendUpNat E Q).some.symm

end Work.DSEQ0
