import Mathlib

namespace Work.ANALYTIC.CechGen

open CategoryTheory Limits
universe u v u' v'

/-- Naturality of Mathlib's `HomologicalComplex.extendSingleIso` in the object `X`: extending the
map of single complexes induced by `g : X ⟶ Y` along an embedding `e : c.Embedding c'` is the same
as conjugating `(single C c' i').map g` by the isomorphisms `extendSingleIso`.  (Mathlib has
`HomologicalComplex.extendSingleIso_hom_f` but not this naturality statement; the proof is a
component computation, all components off `i'` being zero.) -/
theorem extendSingleIso_naturality {C : Type u} [Category.{v} C] [HasZeroObject C]
    [HasZeroMorphisms C] {ι : Type u'} {ι' : Type v'} {c : ComplexShape ι} {c' : ComplexShape ι'}
    [DecidableEq ι] [DecidableEq ι'] (e : c.Embedding c') (i : ι) (i' : ι') (h : e.f i = i')
    {X Y : C} (g : X ⟶ Y) :
    HomologicalComplex.extendMap ((HomologicalComplex.single C c i).map g) e ≫
        (HomologicalComplex.extendSingleIso e Y i i' h).hom =
      (HomologicalComplex.extendSingleIso e X i i' h).hom ≫
        (HomologicalComplex.single C c' i').map g := by
  -- Both sides are morphisms `((single C c i).obj X).extend e ⟶ (single C c' i').obj Y`,
  -- and the target is concentrated in degree `i'`, so it suffices to compare the `i'`-components.
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  -- Replace the component of the extension map and of `single.map` by their explicit formulas.
  have h1 := HomologicalComplex.extendMap_f
    (φ := (HomologicalComplex.single C c i).map g) (e := e) h
  have h2 := HomologicalComplex.extendSingleIso_hom_f (e := e) (X := Y) (i := i) (i' := i') h
  have h3 := HomologicalComplex.extendSingleIso_hom_f (e := e) (X := X) (i := i) (i' := i') h
  have h4 := HomologicalComplex.single_map_f_self (c := c') i' g
  have h5 := HomologicalComplex.single_map_f_self (c := c) i g
  rw [h1, h2, h3, h4, h5]
  -- The two occurrences of `extendXIso` on `(single C c i).obj Y` cancel, as do the two
  -- occurrences of `singleObjXSelf c' i' X`.
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Work.ANALYTIC.CechGen
