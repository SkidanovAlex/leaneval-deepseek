/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area GC — the gluing datum of the group chunk

The transition morphisms `t i j : U i j ⟶ U j i` are isomorphisms between the intersections of
the charts, and they satisfy the cocycle condition on triple intersections.  Hence the charts
`V ⊆ Sym^g C` can be glued along them.

Everything in this file is stated at the level of plain schemes (`Scheme.GlueData`), because
the `Over`-level formulation (`CategoryTheory.GlueData (Sch K)`) makes the *kernel* work on
`Opens.toOver`-unfolding defeq problems blow up.
-/
import Mathlib
import Submission.Work.GroupChunk.Gluing.Cocycle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K]
variable {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]

/-- The forgetful functor `Sch K ⥤ Scheme`. -/
abbrev fgt (K : Type u) [Field K] : Sch K ⥤ Scheme := Over.forget (Spec (CommRingCat.of K))

/-- The chart `V`, as a plain scheme. -/
abbrev Vsch (D : Input C P0) : Scheme := (Opens.toOver D.V).left

/-- The transition domain `U i j`, as a plain scheme. -/
abbrev Usch (D : Input C P0) (i j : D.Idx) : Scheme :=
  (Work.GroupChunk.U (D := D) i j : Scheme)

/-- The inclusion `U i j ⟶ V` of the transition domain into the chart. -/
abbrev Uinc (D : Input C P0) (i j : D.Idx) : Usch D i j ⟶ Vsch D :=
  (Work.GroupChunk.U (D := D) i j).ι

/-- The triple intersection `Pb i j k`, as a plain scheme. -/
abbrev PbSch (D : Input C P0) (i j k : D.Idx) : Scheme := (Pb (D := D) i j k).left

theorem isIso_ι_top (X : Scheme) : IsIso (⊤ : X.Opens).ι :=
  IsIso.mk' ⟨X.topIso.inv, Scheme.toIso_inv_ι X, Scheme.ι_toIso_inv X⟩

/-- The canonical isomorphism between the pullback in `Sch K` (computed in `Over (Spec K)`)
and the pullback of the underlying scheme morphisms. -/
abbrev pbIso (D : Input C P0) (i j k : D.Idx) :
    PbSch D i j k ≅ pullback (Uinc D i j) (Uinc D i k) :=
  PreservesPullback.iso (fgt K) (Opens.ιOver (Work.GroupChunk.U (D := D) i j))
    (Opens.ιOver (Work.GroupChunk.U (D := D) i k))

/-- The transition morphism `U i j ⟶ U j i`. -/
abbrev trSch (D : Input C P0) (i j : D.Idx) : Usch D i j ⟶ Usch D j i :=
  (tr (D := D) i j).left

/-- The transition on triple intersections, transported to plain schemes. -/
abbrev tr'Sch (D : Input C P0) (i j k : D.Idx) :
    pullback (Uinc D i j) (Uinc D i k) ⟶ pullback (Uinc D j k) (Uinc D j i) :=
  (pbIso D i j k).inv ≫ (tr' (D := D) i j k).left ≫ (pbIso D j k i).hom

theorem trSch_self (D : Input C P0) (i : D.Idx) : trSch D i i = 𝟙 (Usch D i i) := by
  have h := congrArg Over.Hom.left (tr_self (D := D) i)
  rw [Over.id_left] at h
  exact h

/-- Conjugation of a triple product of composable morphisms by isomorphisms. -/
theorem conj_cocycle {A B C A' B' C' : Scheme} (E₁ : A ≅ A') (E₂ : B ≅ B') (E₃ : C ≅ C')
    (U : A ⟶ B) (V : B ⟶ C) (W : C ⟶ A) (h : U ≫ V ≫ W = 𝟙 A) :
    (E₁.inv ≫ U ≫ E₂.hom) ≫ (E₂.inv ≫ V ≫ E₃.hom) ≫ (E₃.inv ≫ W ≫ E₁.hom) = 𝟙 A' := by
  calc (E₁.inv ≫ U ≫ E₂.hom) ≫ (E₂.inv ≫ V ≫ E₃.hom) ≫ (E₃.inv ≫ W ≫ E₁.hom)
      = E₁.inv ≫ (U ≫ V ≫ W) ≫ E₁.hom := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = E₁.inv ≫ 𝟙 A ≫ E₁.hom := by rw [h]
    _ = 𝟙 A' := by simp

theorem tr'_facSch (D : Input C P0) (i j k : D.Idx) :
    tr'Sch D i j k ≫ pullback.snd (Uinc D j k) (Uinc D j i)
      = pullback.fst (Uinc D i j) (Uinc D i k) ≫ trSch D i j := by
  have h : (tr' (D := D) i j k).left ≫ (pbSnd (D := D) j k i).left
      = (pbFst (D := D) i j k).left ≫ (tr (D := D) i j).left := by
    have h0 := congrArg Over.Hom.left (tr'_fac (D := D) i j k)
    simpa only [Over.comp_left] using h0
  have h1 : (pbIso D j k i).hom ≫ pullback.snd (Uinc D j k) (Uinc D j i)
      = (pbSnd (D := D) j k i).left := by
    rw [show (pbIso D j k i).hom
        = (PreservesPullback.iso (fgt K) (Opens.ιOver (Work.GroupChunk.U (D := D) j k))
            (Opens.ιOver (Work.GroupChunk.U (D := D) j i))).hom from rfl]
    exact PreservesPullback.iso_hom_snd (fgt K)
      (Opens.ιOver (Work.GroupChunk.U (D := D) j k))
      (Opens.ιOver (Work.GroupChunk.U (D := D) j i))
  have h2 : (pbIso D i j k).inv ≫ (pbFst (D := D) i j k).left
      = pullback.fst (Uinc D i j) (Uinc D i k) := by
    rw [show (pbIso D i j k).inv
        = (PreservesPullback.iso (fgt K) (Opens.ιOver (Work.GroupChunk.U (D := D) i j))
            (Opens.ιOver (Work.GroupChunk.U (D := D) i k))).inv from rfl]
    exact PreservesPullback.iso_inv_fst (fgt K)
      (Opens.ιOver (Work.GroupChunk.U (D := D) i j))
      (Opens.ιOver (Work.GroupChunk.U (D := D) i k))
  simp only [tr'Sch, Category.assoc]
  rw [h1, h, ← Category.assoc, h2]

theorem tr'_cocycleSch (D : Input C P0) (i j k : D.Idx) :
    tr'Sch D i j k ≫ tr'Sch D j k i ≫ tr'Sch D k i j
      = 𝟙 (pullback (Uinc D i j) (Uinc D i k)) := by
  have hawk : (tr' (D := D) i j k).left ≫ (tr' (D := D) j k i).left
      ≫ (tr' (D := D) k i j).left = 𝟙 (PbSch D i j k) := by
    have h0 := congrArg Over.Hom.left (tr'_cocycle (D := D) i j k)
    simpa only [Over.comp_left, Over.id_left] using h0
  exact conj_cocycle (pbIso D i j k) (pbIso D j k i) (pbIso D k i j)
    (tr' (D := D) i j k).left (tr' (D := D) j k i).left (tr' (D := D) k i j).left hawk

/-- The inclusion of a diagonal transition domain is an isomorphism (`U i i = ⊤`). -/
theorem isIso_ι_Uself (D : Input C P0) (i : D.Idx) :
    IsIso ((Work.GroupChunk.U (D := D) i i).ι) := by
  rw [U_self (D := D) i]
  exact isIso_ι_top (Vsch D)

/-- **The gluing datum of the group chunk**, as glue data of schemes. -/
def glueScheme (D : Input C P0) : Scheme.GlueData where
  J := D.Idx
  U _ := Vsch D
  V ij := Usch D ij.1 ij.2
  f i j := Uinc D i j
  f_mono i j := inferInstance
  f_hasPullback i j k := inferInstance
  f_id i := isIso_ι_Uself D i
  t i j := trSch D i j
  t_id i := trSch_self D i
  t' i j k := tr'Sch D i j k
  t_fac i j k := tr'_facSch D i j k
  cocycle i j k := tr'_cocycleSch D i j k
  f_open i j := inferInstance

/-- The compatibility of the structure morphisms of the charts. -/
theorem gluedHomCompat (D : Input C P0) : ∀ a : D.Idx × D.Idx,
    (glueScheme D).diagram.fst a ≫ (Opens.toOver D.V).hom
      = (glueScheme D).diagram.snd a ≫ (Opens.toOver D.V).hom := by
  rintro ⟨i, j⟩
  show Uinc D i j ≫ (Opens.toOver D.V).hom
      = (trSch D i j ≫ Uinc D j i) ≫ (Opens.toOver D.V).hom
  rw [Category.assoc]
  exact (Over.w (tr (D := D) i j)).symm

/-- The structure morphism of the glued scheme. -/
def gluedHom (D : Input C P0) : (glueScheme D).glued ⟶ Spec (CommRingCat.of K) :=
  Multicoequalizer.desc (glueScheme D).diagram (Spec (CommRingCat.of K))
    (fun _ => (Opens.toOver D.V).hom) (gluedHomCompat D)

theorem gluedHom_π (D : Input C P0) (i : D.Idx) :
    (glueScheme D).ι i ≫ gluedHom D = (Opens.toOver D.V).hom :=
  Multicoequalizer.π_desc (glueScheme D).diagram (Spec (CommRingCat.of K))
    (fun _ => (Opens.toOver D.V).hom) (gluedHomCompat D) i

/-- **The glued group chunk**, as a `K`-scheme. -/
def GSch (D : Input C P0) : Sch K := Over.mk (gluedHom D)

/-- The chart map `V ⟶ GSch`. -/
def chartH (D : Input C P0) (i : D.Idx) : Opens.toOver D.V ⟶ GSch D :=
  Over.homMk ((glueScheme D).ι i) (by
    change (glueScheme D).ι i ≫ gluedHom D = (Opens.toOver D.V).hom
    exact gluedHom_π D i)

theorem chartH_left (D : Input C P0) (i : D.Idx) :
    (chartH D i).left = (glueScheme D).ι i := rfl

end

end Work.GroupChunk
