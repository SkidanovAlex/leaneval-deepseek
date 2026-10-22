import Mathlib
import Submission.Work.CWIND.Basic
import Submission.Work.CWIND.GClass.Prelim

/-!
# CWIND/T9 setup — the exhaustion diagram of an increasing sequence of subspaces

This file records the diagrams (functors `ℕ ⥤ …`) and cocones attached to an increasing sequence
`A : ℕ → Set X` of subsets of a topological space `X`:

* `exhTop` — the diagram `n ↦ X_n = A n` in `TopCat` with transition maps the inclusions;
* `exhTopCocone` — the cocone with point `X`;
* `CsingExh`, `Aexh` — the same diagram in cochain complexes, through the singular chain complex
  and through `A(X) = extend (alternatingFaceMapComplex ℤ[X^{Δ•}])`;
* `CsingExhCocone`, `AexhCocone` — the induced cocones with point `C_sing X` resp. `A(X)`;
* `exhNat` — the natural transformation `CsingExh ⟶ Aexh` induced by `b` (naturality of `b`);
* `SSetExh`, `SSetExhCocone`, `typeExh`, `typeCocone` — the same diagram of singular simplicial
  sets and its degreewise value at `k` (a diagram of types);
* `CsrcExh`, `AchainExh` — the same diagram before extension along `ComplexShape.embeddingDownNat`;
* `sSetLevel`, `Psi` — the functor `Y ↦ (Y.chainComplex ℤ)_k`, and its composite with `discrete`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits LightCondensed LightProfinite
open LightCondensed.Solid Submission.Blueprint
open scoped Simplicial

universe u

namespace Work.CWIND.GClass

open Work.CWIND

/-! ## Colimit instances -/

instance instHasColimitsMod (J : Type) : HasColimitsOfShape (Discrete J) (ModuleCat ℤ) :=
  ModuleCat.hasColimitsOfShape ℤ (Discrete J)

instance instHasColimitsA : HasColimitsOfSize.{0, 0} LightCondAb :=
  IsGrothendieckAbelian.hasColimits LightCondAb

instance instHasCoprodA (J : Type) : HasColimitsOfShape (Discrete J) LightCondAb :=
  HasColimitsOfSize.has_colimits_of_shape (Discrete J)

instance instHasCoprodCpx (J : Type) :
    HasColimitsOfShape (Discrete J) (CochainComplex LightCondAb ℤ) :=
  HomologicalComplex.instHasColimitsOfShape

/-! ## The diagram of subspaces -/

variable {X : TopCat.{0}} (A : ℕ → Set X) (hmono : Monotone A)

/-- The diagram `n ↦ A n` of an increasing sequence of subspaces. -/
def exhTop : ℕ ⥤ TopCat.{0} where
  obj n := TopCat.of (A n)
  map {m n} f := Submission.Blueprint.incl (hmono (leOfHom f))
  map_id m := by
    apply TopCat.ext
    intro x
    rfl
  map_comp {m n k} f g := by
    apply TopCat.ext
    intro x
    rfl

@[simp]
lemma exhTop_obj (n : ℕ) : (exhTop A hmono).obj n = TopCat.of (A n) := rfl

@[simp]
lemma exhTop_map {m n : ℕ} (f : m ⟶ n) :
    (exhTop A hmono).map f = Submission.Blueprint.incl (hmono (leOfHom f)) := rfl

/-- The cocone under `exhTop` with point `X`. -/
def exhTopCocone : Cocone (exhTop A hmono) where
  pt := X
  ι :=
    { app := fun n => Submission.Blueprint.inclTop (A n)
      naturality := by
        intro m n f
        apply TopCat.ext
        intro x
        rfl }

@[simp]
lemma exhTopCocone_pt : (exhTopCocone A hmono).pt = X := rfl

@[simp]
lemma exhTopCocone_ι_app (n : ℕ) :
    (exhTopCocone A hmono).ι.app n = Submission.Blueprint.inclTop (A n) := rfl

/-! ## The exhaustion diagrams of complexes -/

/-- The exhaustion diagram of singular chain complexes. -/
abbrev CsingExh : ℕ ⥤ CochainComplex LightCondAb ℤ :=
  exhTop A hmono ⋙ singularChainsLightCondAbComplexFunctor

/-- The exhaustion diagram of the complexes `A(A n)`. -/
abbrev Aexh : ℕ ⥤ CochainComplex LightCondAb ℤ :=
  exhTop A hmono ⋙ AFunctor

@[simp]
lemma CsingExh_obj (n : ℕ) :
    (CsingExh A hmono).obj n = singularChainsLightCondAbComplexFunctor.obj (TopCat.of (A n)) :=
  rfl

@[simp]
lemma Aexh_obj (n : ℕ) : (Aexh A hmono).obj n = AFunctor.obj (TopCat.of (A n)) := rfl

/-- The exhaustion cocone of singular chain complexes, with point `C_sing(X)`. -/
abbrev CsingExhCocone : Cocone (CsingExh A hmono) :=
  Functor.mapCocone singularChainsLightCondAbComplexFunctor (exhTopCocone A hmono)

/-- The exhaustion cocone of the `A(A n)`, with point `A(X)`. -/
abbrev AexhCocone : Cocone (Aexh A hmono) :=
  Functor.mapCocone AFunctor (exhTopCocone A hmono)

@[simp]
lemma CsingExhCocone_pt :
    (CsingExhCocone A hmono).pt = singularChainsLightCondAbComplexFunctor.obj X := rfl

@[simp]
lemma AexhCocone_pt : (AexhCocone A hmono).pt = AFunctor.obj X := rfl

@[simp]
lemma CsingExhCocone_ι_app (n : ℕ) :
    (CsingExhCocone A hmono).ι.app n =
      singularChainsLightCondAbComplexFunctor.map (Submission.Blueprint.inclTop (A n)) := rfl

@[simp]
lemma AexhCocone_ι_app (n : ℕ) :
    (AexhCocone A hmono).ι.app n =
      AFunctor.map (Submission.Blueprint.inclTop (A n)) := rfl

/-- The natural transformation `CsingExh ⟶ Aexh` induced by a natural transformation
`b : C_sing ⟶ A` (by whiskering). -/
abbrev exhNat (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor) :
    CsingExh A hmono ⟶ Aexh A hmono :=
  Functor.whiskerLeft (exhTop A hmono) b

@[simp]
lemma exhNat_app (b : singularChainsLightCondAbComplexFunctor ⟶ AFunctor) (n : ℕ) :
    (exhNat A hmono b).app n = b.app (TopCat.of (A n)) := rfl

/-! ## The diagrams before extension -/

/-- The singular chain complex functor as a functor into `ℕ`-chain complexes of light condensed
abelian groups. -/
abbrev CsrcFunctor : TopCat.{0} ⥤ ChainComplex LightCondAb ℕ :=
  singC ⋙ (LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)

/-- The exhaustion diagram of `ℕ`-chain complexes of singular chains. -/
abbrev CsrcExh : ℕ ⥤ ChainComplex LightCondAb ℕ := exhTop A hmono ⋙ CsrcFunctor

/-- The exhaustion cocone of `ℕ`-chain complexes of singular chains. -/
abbrev CsrcExhCocone : Cocone (CsrcExh A hmono) :=
  Functor.mapCocone CsrcFunctor (exhTopCocone A hmono)

/-- The exhaustion diagram of `ℕ`-chain complexes of the `A`-complexes. -/
abbrev AchainExh : ℕ ⥤ ChainComplex LightCondAb ℕ := exhTop A hmono ⋙ AchainFunctor

/-- The exhaustion cocone of `ℕ`-chain complexes of the `A`-complexes. -/
abbrev AchainExhCocone : Cocone (AchainExh A hmono) :=
  Functor.mapCocone AchainFunctor (exhTopCocone A hmono)

/-! ## The diagrams of (simplicial) sets -/

/-- The exhaustion diagram of singular simplicial sets. -/
abbrev SSetExh : ℕ ⥤ SSet.{0} := exhTop A hmono ⋙ TopCat.toSSet

/-- The exhaustion cocone of singular simplicial sets, with point `Sing(X)`. -/
abbrev SSetExhCocone : Cocone (SSetExh A hmono) :=
  Functor.mapCocone TopCat.toSSet (exhTopCocone A hmono)

@[simp]
lemma SSetExh_obj (n : ℕ) :
    (SSetExh A hmono).obj n = TopCat.toSSet.obj (TopCat.of (A n)) := rfl

@[simp]
lemma SSetExhCocone_pt : (SSetExhCocone A hmono).pt = TopCat.toSSet.obj X := rfl

@[simp]
lemma SSetExhCocone_ι_app (n : ℕ) :
    (SSetExhCocone A hmono).ι.app n =
      TopCat.toSSet.map (Submission.Blueprint.inclTop (A n)) := rfl

/-- The degreewise value at `k` of the exhaustion diagram of simplicial sets. -/
abbrev typeExh (k : ℕ) : ℕ ⥤ Type :=
  SSetExh A hmono ⋙ (evaluation (SimplexCategoryᵒᵖ) (Type)).obj (Opposite.op ⦋k⦌)

/-- The degreewise value at `k` of the exhaustion cocone of simplicial sets, as a cocone of
types. -/
abbrev typeCocone (k : ℕ) : Cocone (typeExh A hmono k) :=
  ((evaluation (SimplexCategoryᵒᵖ) (Type)).obj (Opposite.op ⦋k⦌)).mapCocone
    (SSetExhCocone A hmono)

/-! ## The functors `Y ↦ (Y.chainComplex ℤ)_k` and `Y ↦ ℤ{(Y.chainComplex ℤ)_k}` -/

/-- The `k`-th simplicial chain module of a simplicial set, as a functor. -/
abbrev sSetLevel (k : ℕ) : SSet.{0} ⥤ ModuleCat ℤ :=
  (SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) ⋙
    HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) k

/-- The same, pushed forward to light condensed abelian groups. -/
abbrev Psi (k : ℕ) : SSet.{0} ⥤ LightCondAb :=
  sSetLevel k ⋙ LightCondensed.discrete (ModuleCat ℤ)

/-- The functor of `sSetLevel`, in the form supplied by Mathlib's adjunction. -/
abbrev sSetLevel' (k : ℕ) : SSet.{0} ⥤ ModuleCat ℤ :=
  ((Functor.postcompose₂.obj
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) k)).obj
    (SSet.chainComplexFunctor (ModuleCat ℤ))).obj (ModuleCat.of ℤ ℤ)

lemma sSetLevel_eq (k : ℕ) : sSetLevel k = sSetLevel' k := rfl

@[simp]
lemma sSetLevel_obj (k : ℕ) (Y : SSet.{0}) :
    (sSetLevel k).obj Y = (Y.chainComplex (ModuleCat.of ℤ ℤ)).X k := rfl

@[simp]
lemma CsrcFunctor_obj (Y : TopCat.{0}) : CsrcFunctor.obj Y = Csrc Y := rfl

@[simp]
lemma CsrcFunctor_obj_X (Y : TopCat.{0}) (k : ℕ) :
    (CsrcFunctor.obj Y).X k =
      (LightCondensed.discrete (ModuleCat ℤ)).obj
        (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)).X k) := rfl

@[simp]
lemma Psi_obj_topSSet (k : ℕ) (Y : TopCat.{0}) :
    (Psi k).obj (TopCat.toSSet.obj Y) = (CsrcFunctor.obj Y).X k := rfl

end Work.CWIND.GClass
