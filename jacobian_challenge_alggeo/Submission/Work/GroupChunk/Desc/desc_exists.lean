import Mathlib
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.Transitions
import Submission.Work.GroupChunk.Gluing.Data
import Submission.Work.GroupChunk.Gluing.Transitions

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C] [D : Input C P0]

/-- The transition `t i j` agrees with the gluing transition `tr i j`: both lift the value
`tHom i j` of `σ i j` on `U i j` through the open immersion `Uι j i = U j i ↪ Sym^g C`.

The two morphisms `t i j` and `tr i j` have the same divisor classes at all residue-field
points (`t_cls` and `tq_picOf`), hence agree by injectivity of `picOf` on the chart `V`. -/
theorem t_comp_ιOver (i j : D.Idx) :
    t i j ≫ Opens.ιOver (U j i) = tq i j := by
  apply Work.GCBasics.hom_ext_of_resPt
  intro x
  apply picOf_inj_V j
  change D.picOf j ((resPt (Opens.toOver (U i j)) x ≫ (t i j ≫ Opens.ιOver (U j i)))
      ≫ Opens.ιOver D.V) = D.picOf j ((resPt (Opens.toOver (U i j)) x ≫ tq i j)
        ≫ Opens.ιOver D.V)
  calc D.picOf j ((resPt (Opens.toOver (U i j)) x
          ≫ (t i j ≫ Opens.ιOver (U j i))) ≫ Opens.ιOver D.V)
      = D.picOf j (resPt (Opens.toOver (U i j)) x ≫ t i j ≫ Uι j i) := by
        rw [Uι_def]; simp only [Category.assoc]
    _ = D.picOf i (resPt (Opens.toOver (U i j)) x ≫ Uι i j) := t_cls i j _
    _ = D.picOf j (resPt (Opens.toOver (U i j)) x ≫ tq i j ≫ Opens.ιOver D.V) :=
        (tq_picOf i j _).symm
    _ = D.picOf j ((resPt (Opens.toOver (U i j)) x ≫ tq i j) ≫ Opens.ιOver D.V) := by
        rw [Category.assoc]

variable {Y : Sch K}

/-- The compatibility condition `hφ` of a family `φ i : V ⟶ Y` is exactly the descent
condition for the gluing datum `glueScheme D`: `Uinc i j ≫ φ i = (trSch i j ≫ Uinc j i) ≫ φ j`.

This is `hφ` with the transition `t i j` replaced by the gluing transition `tr i j`
(`t_comp_ιOver`). -/
theorem desc_condition (φ : ∀ i : D.Idx, Opens.toOver D.V ⟶ Y)
    (hφ : ∀ i j : D.Idx,
      Opens.ιOver (U i j) ≫ φ i = (t i j ≫ Opens.ιOver (U j i)) ≫ φ j) :
    ∀ a : D.Idx × D.Idx,
      (glueScheme D).diagram.fst a ≫ (φ a.1).left =
        (glueScheme D).diagram.snd a ≫ (φ a.2).left := by
  rintro ⟨i, j⟩
  have ht : (t i j).left ≫ Uinc D j i = trSch D i j ≫ Uinc D j i := by
    have e1 : (t i j).left ≫ Uinc D j i = (t i j ≫ Opens.ιOver (U j i)).left := by
      rw [Over.comp_left]; rfl
    have e2 : (t i j ≫ Opens.ιOver (U j i)).left = (tq i j).left := by
      rw [t_comp_ιOver]
    have e3 : (tq i j).left = (tr i j ≫ Opens.ιOver (U j i)).left := by rw [tr_ιOver]
    have e4 : (tr i j ≫ Opens.ιOver (U j i)).left = trSch D i j ≫ Uinc D j i := by
      rw [Over.comp_left]; rfl
    rw [e1, e2, e3, e4]
  have h := congrArg Over.Hom.left (hφ i j)
  simp only [Over.comp_left, Category.assoc] at h
  change Uinc D i j ≫ (φ i).left = (trSch D i j ≫ Uinc D j i) ≫ (φ j).left
  rw [← ht, Category.assoc]
  exact h

end

end Work.GroupChunk

namespace Work.GroupChunk.Desc

universe u

open CategoryTheory in
theorem desc_exists {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] [D : Work.GroupChunk.Input C P0] {Y : Work.GCBasics.Sch K}
    (φ : ∀ i : D.Idx, Work.GCBasics.Opens.toOver D.V ⟶ Y)
    (hφ : ∀ i j : D.Idx,
      Work.GCBasics.Opens.ιOver (Work.GroupChunk.U i j) ≫ φ i =
      (Work.GroupChunk.t i j ≫ Work.GCBasics.Opens.ιOver (Work.GroupChunk.U j i)) ≫ φ j) :
    ∃! g : Work.GroupChunk.GSch D ⟶ Y, ∀ i : D.Idx, Work.GroupChunk.chartH D i ≫ g = φ i := by
  have hcond := Work.GroupChunk.desc_condition (D := D) φ hφ
  let gleft : CategoryTheory.Limits.multicoequalizer (Work.GroupChunk.glueScheme D).diagram
      ⟶ Y.left :=
    CategoryTheory.Limits.Multicoequalizer.desc (Work.GroupChunk.glueScheme D).diagram Y.left
      (fun i => (φ i).left) hcond
  have hgleft : ∀ i : D.Idx,
      CategoryTheory.Limits.Multicoequalizer.π (Work.GroupChunk.glueScheme D).diagram i ≫ gleft
        = (φ i).left :=
    fun i => CategoryTheory.Limits.Multicoequalizer.π_desc (Work.GroupChunk.glueScheme D).diagram
      Y.left (fun i => (φ i).left) hcond i
  have hw : gleft ≫ Y.hom = Work.GroupChunk.gluedHom D := by
    apply CategoryTheory.Limits.Multicoequalizer.hom_ext (Work.GroupChunk.glueScheme D).diagram
    intro i
    have hgi := hgleft i
    have hwi : (φ i).left ≫ Y.hom = (Work.GCBasics.Opens.toOver D.V).hom := Over.w (φ i)
    have hgl : CategoryTheory.Limits.Multicoequalizer.π (Work.GroupChunk.glueScheme D).diagram i
        ≫ Work.GroupChunk.gluedHom D = (Work.GCBasics.Opens.toOver D.V).hom :=
      Work.GroupChunk.gluedHom_π D i
    have e0 : CategoryTheory.Limits.Multicoequalizer.π (Work.GroupChunk.glueScheme D).diagram i
          ≫ (gleft ≫ Y.hom)
        = (CategoryTheory.Limits.Multicoequalizer.π (Work.GroupChunk.glueScheme D).diagram i
            ≫ gleft) ≫ Y.hom :=
      (Category.assoc _ _ _).symm
    have e1 : (CategoryTheory.Limits.Multicoequalizer.π (Work.GroupChunk.glueScheme D).diagram i
          ≫ gleft) ≫ Y.hom = (φ i).left ≫ Y.hom :=
      congrArg (· ≫ Y.hom) hgi
    exact e0.trans (e1.trans (hwi.trans hgl.symm))
  refine ⟨Over.homMk gleft hw, ?_, ?_⟩
  · intro i
    apply Over.OverMorphism.ext
    show CategoryTheory.Limits.Multicoequalizer.π (Work.GroupChunk.glueScheme D).diagram i
        ≫ gleft = (φ i).left
    exact hgleft i
  · intro g' hg'
    apply Over.OverMorphism.ext
    show g'.left = gleft
    apply CategoryTheory.Limits.Multicoequalizer.hom_ext (Work.GroupChunk.glueScheme D).diagram
    intro i
    have h1 : CategoryTheory.Limits.Multicoequalizer.π (Work.GroupChunk.glueScheme D).diagram i
        ≫ g'.left = (φ i).left := by
      have hh := congrArg Over.Hom.left (hg' i)
      rw [Over.comp_left] at hh
      exact hh
    exact h1.trans (hgleft i).symm

end Work.GroupChunk.Desc
