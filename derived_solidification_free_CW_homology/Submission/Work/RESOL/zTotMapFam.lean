/-
AREA RESOL — the functoriality of the hand-rolled total complex `Zero.totFull` of the
column-wise resolution of a complex.

This file proves the three component lemmas needed to assemble `Zero.R F π hπ : Cpx ⥤ Cpx`
(see `RESOL/ZeroRes.lean`): the functoriality map `Zero.totMapFam` is the identity on
identities, compatible with composition, and a chain map.  All three are gathered in the
single theorem `Work.RESOL.zTotMapFam`.

Route: `Zero.totX P B n` is the coproduct `∐ (totFam P B n)` indexed by
`TotIdx P n = {x : ℤ × ℤ // x.2 + x.1 = n ∧ P x.1}`, where `x.1` is the *column* (`q`, the
index in `B`) and `x.2` the resolution degree (`p`) inside the column.  The differential
`totDc` splits as `totVpart + totHpart`: the vertical part is the differential of the
resolution `Rco.obj (B.X q)` at degree `p` (a fixed column), the horizontal part is the
differential of `B` with the sign `sgn p = (-1)^p`.

* `ztm_ι` is the component formula `totMapFam` (definitionally `Sigma.ι_comp_desc`).
* `ztm_V` and `ztm_H` compare the vertical and horizontal parts of `totDc` with
  `totMapFam`, using the chain-map property of `Rco.map (f.f q)` and the functoriality of
  `Rco` (`Rco.map (B.d ≫ f.f) = Rco.map (B.d) ≫ Rco.map (f.f)`).
* `ztm_id`, `ztm_comp` are the functoriality axioms, and `ztm_Dc` is the chain-map property
  for `totDc`; `ztm_d_eq` identifies `(totFull B).d n (n+1)` with `totDc B n`.
-/
import Mathlib
import Submission.Work.RESOL.ZeroTotal

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

namespace Zero

/-- The component formula for the functoriality map of the total complex: on the summand
`x = (q, p)` it is `Rco.map (f.f q)` in degree `p`. -/
private lemma ztm_ι {F : LightCondAb ⥤ LightCondAb} [F.PreservesZeroMorphisms]
    {π : F ⟶ 𝟭 LightCondAb} {hπ : ∀ M, Epi (π.app M)}
    {B B' : Cpx} (f : B ⟶ B') (n : ℤ) (x : TotIdx topP n) :
    Sigma.ι (totFam F π hπ topP B n) x ≫ totMapFam F π hπ f n
      = ((Rco F π hπ).map (f.f x.1.1)).f x.1.2
          ≫ Sigma.ι (totFam F π hπ topP B' n) x :=
  Sigma.ι_comp_desc _ x

/-- The differential of `totFull` in degrees `(n, n+1)` is the canonical `totDc`. -/
private lemma ztm_d_eq {F : LightCondAb ⥤ LightCondAb} [F.PreservesZeroMorphisms]
    {π : F ⟶ 𝟭 LightCondAb} {hπ : ∀ M, Epi (π.app M)} (B : Cpx) (n : ℤ) :
    (totFull F π hπ B).d n (n + 1) = totDc F π hπ topP topP_step B n := by
  rw [show (totFull F π hπ B).d n (n + 1)
      = dite (n + 1 = n + 1) (fun h => totD F π hπ topP topP_step B n (n + 1) h)
          (fun _ => 0) from rfl]
  rw [dite_eq_left rfl]
  rfl

/-- The functoriality map is the identity on identities. -/
private lemma ztm_id {F : LightCondAb ⥤ LightCondAb} [F.PreservesZeroMorphisms]
    {π : F ⟶ 𝟭 LightCondAb} {hπ : ∀ M, Epi (π.app M)} (B : Cpx) (n : ℤ) :
    totMapFam F π hπ (𝟙 B) n = 𝟙 ((totFull F π hπ B).X n) := by
  apply Sigma.hom_ext
  intro x
  rw [totMapFam, Sigma.ι_comp_desc]
  erw [Category.comp_id]
  rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, HomologicalComplex.id_f]
  erw [Category.id_comp]

/-- The functoriality map is compatible with composition. -/
private lemma ztm_comp {F : LightCondAb ⥤ LightCondAb} [F.PreservesZeroMorphisms]
    {π : F ⟶ 𝟭 LightCondAb} {hπ : ∀ M, Epi (π.app M)}
    {B B' B'' : Cpx} (f : B ⟶ B') (g : B' ⟶ B'') (n : ℤ) :
    totMapFam F π hπ (f ≫ g) n = totMapFam F π hπ f n ≫ totMapFam F π hπ g n := by
  apply Sigma.hom_ext
  intro x
  rw [ztm_ι (f ≫ g) n x]
  conv_rhs => rw [← Category.assoc]
  rw [ztm_ι f n x, Category.assoc, ztm_ι g n x]
  rw [HomologicalComplex.comp_f, CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    Category.assoc]

/-- The vertical part of `totDc` (the differential of the resolution of `B.X q`, in a fixed
column) commutes with the functoriality map. -/
private lemma ztm_V {F : LightCondAb ⥤ LightCondAb} [F.PreservesZeroMorphisms]
    {π : F ⟶ 𝟭 LightCondAb} {hπ : ∀ M, Epi (π.app M)}
    {B B' : Cpx} (f : B ⟶ B') (n : ℤ) (x : TotIdx topP n) :
    ((Rco F π hπ).map (f.f x.1.1)).f x.1.2 ≫ totVpart F π hπ topP B' n x
      = totVpart F π hπ topP B n x ≫ totMapFam F π hπ f (n + 1) := by
  rw [totVpart, totVpart]
  erw [Category.assoc]
  erw [ztm_ι f (n + 1) (totVIdx x)]
  conv_lhs => erw [← Category.assoc]
  conv_lhs => erw [HomologicalComplex.Hom.comm ((Rco F π hπ).map (f.f x.1.1)) x.1.2 (x.1.2 + 1)]
  conv_lhs => erw [Category.assoc]
  rfl

/-- The horizontal part of `totDc` (the differential of `B`, with signs) commutes with the
functoriality map. -/
private lemma ztm_H {F : LightCondAb ⥤ LightCondAb} [F.PreservesZeroMorphisms]
    {π : F ⟶ 𝟭 LightCondAb} {hπ : ∀ M, Epi (π.app M)}
    {B B' : Cpx} (f : B ⟶ B') (n : ℤ) (x : TotIdx topP n) :
    ((Rco F π hπ).map (f.f x.1.1)).f x.1.2 ≫ totHpart F π hπ topP topP_step B' n x
      = totHpart F π hπ topP topP_step B n x ≫ totMapFam F π hπ f (n + 1) := by
  rw [totHpart, totHpart]
  rw [Linear.comp_units_smul, Linear.units_smul_comp]
  apply congrArg (fun t => sgn x.1.2 • t)
  have hmap : ((Rco F π hπ).map (f.f x.1.1)).f x.1.2
      ≫ ((Rco F π hπ).map (B'.d x.1.1 (x.1.1 + 1))).f x.1.2
      = ((Rco F π hπ).map (B.d x.1.1 (x.1.1 + 1))).f x.1.2
        ≫ ((Rco F π hπ).map (f.f (x.1.1 + 1))).f x.1.2 := by
    rw [← HomologicalComplex.comp_f, ← CategoryTheory.Functor.map_comp,
      HomologicalComplex.Hom.comm f x.1.1 (x.1.1 + 1), CategoryTheory.Functor.map_comp,
      HomologicalComplex.comp_f]
  erw [Category.assoc]
  erw [ztm_ι f (n + 1) (totHIdx topP_step x)]
  conv_lhs => erw [← Category.assoc]
  rw [hmap]
  conv_lhs => erw [Category.assoc]
  rfl

/-- The functoriality map is a chain map for the canonical differential `totDc`. -/
private lemma ztm_Dc {F : LightCondAb ⥤ LightCondAb} [F.PreservesZeroMorphisms]
    {π : F ⟶ 𝟭 LightCondAb} {hπ : ∀ M, Epi (π.app M)}
    {B B' : Cpx} (f : B ⟶ B') (n : ℤ) :
    totMapFam F π hπ f n ≫ totDc F π hπ topP topP_step B' n
      = totDc F π hπ topP topP_step B n ≫ totMapFam F π hπ f (n + 1) := by
  apply Sigma.hom_ext
  intro x
  conv_lhs => rw [← Category.assoc, ztm_ι f n x, Category.assoc, totDc_apply,
    Preadditive.comp_add]
  conv_rhs => rw [← Category.assoc, totDc_apply, Preadditive.add_comp]
  rw [ztm_V f n x, ztm_H f n x]

end Zero

theorem zTotMapFam (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M, CategoryTheory.Epi (π.app M)) :
    (∀ (B : Work.RESOL.Cpx) (n : ℤ),
        Work.RESOL.Zero.totMapFam F π hπ (CategoryTheory.CategoryStruct.id B) n
          = CategoryTheory.CategoryStruct.id ((Work.RESOL.Zero.totFull F π hπ B).X n))
    ∧ (∀ (B B' B'' : Work.RESOL.Cpx) (f : B ⟶ B') (g : B' ⟶ B'') (n : ℤ),
        Work.RESOL.Zero.totMapFam F π hπ (CategoryTheory.CategoryStruct.comp f g) n
          = CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.totMapFam F π hπ f n)
              (Work.RESOL.Zero.totMapFam F π hπ g n))
    ∧ (∀ (B B' : Work.RESOL.Cpx) (f : B ⟶ B') (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j),
        CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.totMapFam F π hπ f i)
            ((Work.RESOL.Zero.totFull F π hπ B').d i j)
          = CategoryTheory.CategoryStruct.comp ((Work.RESOL.Zero.totFull F π hπ B).d i j)
              (Work.RESOL.Zero.totMapFam F π hπ f j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B n
    exact Zero.ztm_id B n
  · intro B B' B'' f g n
    exact Zero.ztm_comp f g n
  · intro B B' f i j hij
    have hj : i + 1 = j := (ComplexShape.up_Rel ℤ i j).mp hij
    subst hj
    rw [Zero.ztm_d_eq B' i, Zero.ztm_d_eq B i]
    exact Zero.ztm_Dc f i

end Work.RESOL
