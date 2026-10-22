import Mathlib
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Instances

/-!
# Quasi-isomorphisms are stable under exact colimits

`LightCondAb` is a Grothendieck abelian category, so small coproducts (AB4) and, more
generally, every shape `J` of colimits whose colimits are exact in `LightCondAb`
(`HasExactColimitsOfShape J LightCondAb`) are exact.  Consequently the coproduct of a family
of quasi-isomorphisms of cochain complexes of light condensed abelian groups is again a
quasi-isomorphism; the coproduct case is `J = Discrete J'`, where `colimMap τ` is the
coproduct of the maps `τ j`.

The mathematical content is that the functor `colim : (J ⥤ LightCondAb) ⥤ LightCondAb` is
exact: it is a left adjoint (so it preserves finite colimits) and, by hypothesis, it preserves
finite limits, hence it preserves homology.  Applying this to the "transposed" complexes of
functors (`transposeComplex`, which views `F : J ⥤ Cpx` as a single complex of functors)
identifies the colimit of `F` in `Cpx` with the degreewise colimit of `F`, and `colimMap τ`
with the map induced by `τ` degreewise.  The result then follows from
`HomologicalComplex.quasiIso_map_of_preservesHomology` and
`HomologicalComplex.quasiIso_iff_evaluation`.

## Main result

* `Work.TOOLKIT.Coprod.quasiIso_colimMap`
-/

open CategoryTheory Limits LightProfinite LightCondensed

noncomputable section

namespace Work.TOOLKIT.Coprod

/-- View a functor `F : J ⥤ Cpx` as a single complex of functors `J ⥤ LightCondAb`:
the degree `n` part is `F` composed with the evaluation at `n`.  This is the "transpose"
of a family of complexes, and is the bridge between the category `J ⥤ Cpx` and the category
`CochainComplex (J ⥤ LightCondAb) ℤ`. -/
noncomputable abbrev transposeComplex {J : Type} [Category J] (F : J ⥤ Cpx) :
    CochainComplex (J ⥤ LightCondAb) ℤ where
  X n := F ⋙ HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) n
  d n m := { app := fun j => (F.obj j).d n m
             naturality := fun j j' φ => HomologicalComplex.Hom.comm (F.map φ) n m }
  shape n m h := NatTrans.ext (funext fun j => (F.obj j).shape n m h)
  d_comp_d' n m k _ _ := NatTrans.ext (funext fun j => by simp)

/-- The morphism of complexes of functors induced by a natural transformation of families
of complexes; it is the degreewise version of `τ`. -/
noncomputable abbrev transposeMap {J : Type} [Category J] {F G : J ⥤ Cpx} (τ : F ⟶ G) :
    transposeComplex F ⟶ transposeComplex G where
  f n :=
    { app := fun j => (τ.app j).f n
      naturality := fun j j' φ => by
        show (F ⋙ HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) n).map φ ≫ (τ.app j').f n =
             (τ.app j).f n ≫ (G ⋙ HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) n).map φ
        have h := congrArg (fun f => f.f n) (NatTrans.naturality τ φ)
        simp only [HomologicalComplex.comp_f] at h
        simpa only [Functor.comp_map, HomologicalComplex.eval_map] using h }
  comm' n m _ := NatTrans.ext (funext fun j => (τ.app j).comm n m)

/-- The functor `colim : (J ⥤ LightCondAb) ⥤ LightCondAb` prolongated to cochain complexes.
Its value at `transposeComplex F` computes the degreewise colimit description of the colimit
of `F` in `Cpx`. -/
noncomputable abbrev colimOnComplexes {J : Type} [Category J] [HasColimitsOfShape J LightCondAb] :
    CochainComplex (J ⥤ LightCondAb) ℤ ⥤ Cpx :=
  (Limits.colim (J := J) (C := LightCondAb)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The canonical cocone over `F : J ⥤ Cpx` whose point is the degreewise colimit of `F`
and whose structure maps are induced by the colimit inclusions. -/
noncomputable abbrev colimEvalCocone {J : Type} [Category J] [HasColimitsOfShape J LightCondAb]
    (F : J ⥤ Cpx) : Cocone F where
  pt := colimOnComplexes.obj (transposeComplex F)
  ι :=
    { app := fun j =>
        { f := fun n => colimit.ι ((transposeComplex F).X n) j
          comm' := fun n m _ => ι_colimMap ((transposeComplex F).d n m) j }
      naturality := fun j j' φ => by
        apply HomologicalComplex.hom_ext
        intro n
        simp only [HomologicalComplex.comp_f]
        exact colimit.w ((transposeComplex F).X n) φ }

/-- The cocone `colimEvalCocone F` is a colimit cocone: this is the statement that colimits
of complexes are computed degreewise (`HomologicalComplex.isColimitOfEval`). -/
noncomputable abbrev isColimit_colimEvalCocone {J : Type} [Category J]
    [HasColimitsOfShape J LightCondAb] (F : J ⥤ Cpx) : IsColimit (colimEvalCocone F) :=
  HomologicalComplex.isColimitOfEval F (colimEvalCocone F) (fun n =>
    IsColimit.ofIsoColimit (colimit.isColimit ((transposeComplex F).X n))
      (Cocone.ext (Iso.refl _) (fun _ => rfl)))

/-- Coproducts (and more generally colimits of any shape `J` whose colimits are exact in
`LightCondAb`) of quasi-isomorphisms of cochain complexes of light condensed abelian groups are
quasi-isomorphisms.  The coproduct case is the instance `J = Discrete J'`: there
`colimMap τ` is the coproduct of the maps `τ j`.  Route: `colim` preserves finite limits (AB4 /
AB5) and finite colimits (left adjoint), hence homology; see
`HomologicalComplex.quasiIso_map_of_preservesHomology`, `HomologicalComplex.quasiIso_iff_evaluation`
(viewing the family as one complex of functors) and `HomologicalComplex.isColimitOfPreserves`. -/
theorem quasiIso_colimMap {J : Type} [CategoryTheory.Category J]
    [CategoryTheory.Limits.HasColimitsOfShape J LightCondAb]
    [CategoryTheory.HasExactColimitsOfShape J LightCondAb]
    {F G : CategoryTheory.Functor J Work.TOOLKIT.Cpx} (τ : F ⟶ G)
    (hτ : ∀ j, QuasiIso (τ.app j)) :
    QuasiIso (CategoryTheory.Limits.colimMap τ) := by
  -- `τ` is a quasi-isomorphism of complexes of functors, by evaluation in each `j`.
  have hφ : QuasiIso (transposeMap τ) := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro j
    rw [show (((CategoryTheory.evaluation J LightCondAb).obj j).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (transposeMap τ) = τ.app j from rfl]
    exact hτ j
  -- `colim` is exact: it preserves finite limits (hypothesis) and finite colimits (it is a left
  -- adjoint), hence it preserves homology, so it preserves quasi-isomorphisms
  -- (`HomologicalComplex.quasiIso_map_of_preservesHomology`), and `hφ` is a local instance.
  have hψ : QuasiIso (colimOnComplexes.map (transposeMap τ)) := inferInstance
  -- The degreewise colimit map is the map on the canonical colimit cocones induced by `τ`.
  have h1 : ∀ j, (colimEvalCocone F).ι.app j ≫ colimOnComplexes.map (transposeMap τ)
      = τ.app j ≫ (colimEvalCocone G).ι.app j := by
    intro j
    apply HomologicalComplex.hom_ext
    intro n
    simp only [HomologicalComplex.comp_f]
    exact ι_colimMap ((transposeMap τ).f n) j
  -- Comparing the canonical colimit cocones `colimit.cocone` and `colimEvalCocone`, the map
  -- `colimMap τ` corresponds to the degreewise colimit map.
  have hsquare :
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F)
          (isColimit_colimEvalCocone F)).hom ≫ colimOnComplexes.map (transposeMap τ)
      = Limits.colimMap τ ≫
        (IsColimit.coconePointUniqueUpToIso (colimit.isColimit G)
          (isColimit_colimEvalCocone G)).hom := by
    apply IsColimit.hom_ext (colimit.isColimit F)
    intro j
    calc colimit.ι F j ≫ ((IsColimit.coconePointUniqueUpToIso (colimit.isColimit F)
            (isColimit_colimEvalCocone F)).hom ≫ colimOnComplexes.map (transposeMap τ))
        = (colimit.ι F j ≫ (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F)
            (isColimit_colimEvalCocone F)).hom) ≫ colimOnComplexes.map (transposeMap τ) :=
          (Category.assoc _ _ _).symm
      _ = (colimEvalCocone F).ι.app j ≫ colimOnComplexes.map (transposeMap τ) :=
          congrArg (fun x => x ≫ colimOnComplexes.map (transposeMap τ))
            (IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F)
              (isColimit_colimEvalCocone F) j)
      _ = τ.app j ≫ (colimEvalCocone G).ι.app j := h1 j
      _ = τ.app j ≫ (colimit.ι G j ≫ (IsColimit.coconePointUniqueUpToIso (colimit.isColimit G)
            (isColimit_colimEvalCocone G)).hom) :=
          (congrArg (fun x => τ.app j ≫ x)
            (IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit G)
              (isColimit_colimEvalCocone G) j)).symm
      _ = (τ.app j ≫ colimit.ι G j) ≫ (IsColimit.coconePointUniqueUpToIso (colimit.isColimit G)
            (isColimit_colimEvalCocone G)).hom := (Category.assoc _ _ _).symm
      _ = (colimit.ι F j ≫ Limits.colimMap τ) ≫ (IsColimit.coconePointUniqueUpToIso
            (colimit.isColimit G) (isColimit_colimEvalCocone G)).hom := by rw [ι_colimMap]
      _ = colimit.ι F j ≫ (Limits.colimMap τ ≫ (IsColimit.coconePointUniqueUpToIso
            (colimit.isColimit G) (isColimit_colimEvalCocone G)).hom) := Category.assoc _ _ _
  -- Transfer quasi-isomorphism along the isomorphism of arrows.
  exact quasiIso_of_arrow_mk_iso (colimOnComplexes.map (transposeMap τ)) (Limits.colimMap τ)
    (Arrow.isoMk (IsColimit.coconePointUniqueUpToIso (colimit.isColimit F)
        (isColimit_colimEvalCocone F))
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit G) (isColimit_colimEvalCocone G))
      hsquare).symm

end Work.TOOLKIT.Coprod
