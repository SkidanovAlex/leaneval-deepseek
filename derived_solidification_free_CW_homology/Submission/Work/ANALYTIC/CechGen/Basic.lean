/-
# The free Čech complex of an epimorphism of light condensed sets, arbitrary source

This module generalises the definitions of `Submission/Work/ANALYTIC/CechPt/Nerve.lean` (which are
stated for a source that is a *light profinite* set) to an arbitrary light condensed set `X`, and
sets up the *comparison* of the Čech complexes attached to a morphism of arrows

```
X' --u--> X
|β'       |β
v         v
Y' --v--> Y
```

The chain of constructions is:

* `nerve β = Arrow.cechNerve (Arrow.mk β) : SimplicialObject LightCondSet`, with level `p` the
  `(p+1)`-fold wide pullback of `X` over `Y`;
* `freeNerve β = nerve β ⋙ free ℤ : SimplicialObject LightCondAb`;
* `cechCpx β`, the alternating-face-map complex of `freeNerve β`, transported to the cohomological
  indexing `up ℤ` along `ComplexShape.embeddingDownNat` (so it is concentrated in degrees `≤ 0`,
  cf. `isZero_cechCpx_X_of_pos`);
* `cechAug β : cechCpx β ⟶ sng₀ ℤ[Y]`, the augmentation;
* `cechCmp u v huv : cechCpx β' ⟶ cechCpx β`, the comparison induced by a morphism of arrows, whose
  degree components are computed in `cechCmp_f`;
* `solidEquiv_cechCmp`, the levelwise comparison of the two Čech complexes, from the levelwise
  hypotheses on the Čech nerve (`ToolkitProp.levelwise`);
* `quasiIso_cechAug_of` and `solidEquiv_cechAug_of`, the descent inputs, with the two mathematical
  ingredients (degree-`0` and higher-degree acyclicity) passed as explicit hypotheses;
* `cechAug_naturality`, the commuting square `cechCmp ≫ cechAug β = cechAug β' ≫ sng₀ ℤ[v]` (with
  the naturality of `HomologicalComplex.extendSingleIso` passed as an explicit hypothesis).
-/
import Mathlib
import ChallengeDeps
import Submission.Work.TOOLKIT.Main

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ANALYTIC.CechGen

open Submission.Blueprint

/-- The alternating-face-map complex functor on simplicial abelian groups. -/
abbrev afmc : SimplicialObject LightCondAb ⥤ ChainComplex LightCondAb ℕ :=
  AlgebraicTopology.alternatingFaceMapComplex LightCondAb

/-- The canonical condition `embeddingDownNat.f 0 = 0`, in named form so that the proof term
occurring in `eiso` is stable and can be matched syntactically. -/
theorem embeddingDownNat_zero : ComplexShape.embeddingDownNat.f 0 = 0 :=
  ComplexShape.embeddingDownNat_f 0

/-- The extension of a single complex along `down ℕ ↪ up ℤ` is the corresponding single complex. -/
noncomputable abbrev eiso (A : LightCondAb) :
    (((HomologicalComplex.single LightCondAb (ComplexShape.down ℕ) 0).obj A).extend
        ComplexShape.embeddingDownNat) ≅
      (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj A :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat A 0 0 embeddingDownNat_zero

/-- The Čech nerve of a morphism of light condensed sets, as a simplicial object. -/
noncomputable abbrev nerve {X Y : LightCondSet.{0}} (β : X ⟶ Y) :
    SimplicialObject LightCondSet.{0} :=
  Arrow.cechNerve (Arrow.mk β)

/-- The free light condensed abelian group on the Čech nerve: `p ↦ ℤ[X ×_Y ⋯ ×_Y X]`. -/
noncomputable abbrev freeNerve {X Y : LightCondSet.{0}} (β : X ⟶ Y) :
    SimplicialObject LightCondAb :=
  nerve β ⋙ free ℤ

/-- The Čech complex of `β`, as a cochain complex concentrated in degrees `≤ 0`: degree `-p` is
`ℤ` on the `p`-th term of the Čech nerve. -/
noncomputable abbrev cechCpx {X Y : LightCondSet.{0}} (β : X ⟶ Y) :
    CochainComplex LightCondAb ℤ :=
  (afmc.obj (freeNerve β)).extend ComplexShape.embeddingDownNat

/-- The chain-level augmentation of the Čech complex, as a morphism of `ℕ`-graded chain
complexes. -/
noncomputable abbrev cechEps {X Y : LightCondSet.{0}} (β : X ⟶ Y) :
    afmc.obj (freeNerve β) ⟶ (ChainComplex.single₀ LightCondAb).obj ((free ℤ).obj Y) :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    ((SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).obj
      (Arrow.augmentedCechNerve (Arrow.mk β)))

/-- The augmentation of the Čech complex of `β`: `cechCpx β ⟶ ℤ[Y]` concentrated in degree `0`. -/
noncomputable def cechAug {X Y : LightCondSet.{0}} (β : X ⟶ Y) : cechCpx β ⟶
    (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).obj ((free ℤ).obj Y) :=
  HomologicalComplex.extendMap (cechEps β) ComplexShape.embeddingDownNat ≫
    (eiso ((free ℤ).obj Y)).hom

/-- The morphism of Čech nerves induced by a morphism of arrows. -/
noncomputable abbrev nerveMap {X X' Y Y' : LightCondSet.{0}} (β : X ⟶ Y) (β' : X' ⟶ Y')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (huv : u ≫ β = β' ≫ v) : nerve β' ⟶ nerve β :=
  Arrow.mapCechNerve (Arrow.homMk (f := Arrow.mk β') (g := Arrow.mk β) u v huv)

/-- The level-`p` map of the Čech nerves attached to a morphism of arrows.  This is exactly the map
appearing in the hypothesis of `solidEquiv_of_levelwise_cech`. -/
noncomputable abbrev levelMap {X X' Y Y' : LightCondSet.{0}} (β : X ⟶ Y) (β' : X' ⟶ Y')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (huv : u ≫ β = β' ≫ v) (p : ℕ) :
    (nerve β').obj (Opposite.op (SimplexCategory.mk p)) ⟶
      (nerve β).obj (Opposite.op (SimplexCategory.mk p)) :=
  (Arrow.mapCechNerve
    (Arrow.homMk (f := Arrow.mk β') (g := Arrow.mk β) u v huv)).app
      (Opposite.op (SimplexCategory.mk p))

/-- The comparison of the free Čech nerves, as a map of simplicial abelian groups. -/
noncomputable abbrev freeNerveMap {X X' Y Y' : LightCondSet.{0}} (β : X ⟶ Y) (β' : X' ⟶ Y')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (huv : u ≫ β = β' ≫ v) : freeNerve β' ⟶ freeNerve β :=
  Functor.whiskerRight (nerveMap β β' u v huv) (free ℤ)

/-- The comparison of the Čech complexes attached to a morphism of arrows. -/
noncomputable abbrev cechCmp {X X' Y Y' : LightCondSet.{0}} (β : X ⟶ Y) (β' : X' ⟶ Y')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (huv : u ≫ β = β' ≫ v) : cechCpx β' ⟶ cechCpx β :=
  HomologicalComplex.extendMap (afmc.map (freeNerveMap β β' u v huv))
    ComplexShape.embeddingDownNat

/-! ## The degreewise description of the comparison map -/

/-- The canonical identification of degree `-p` of the Čech complex with the level-`p` term of the
Čech nerve. -/
noncomputable abbrev srcIso {X Y : LightCondSet.{0}} (β : X ⟶ Y) (p : ℕ) :
    (cechCpx β).X (-(p : ℤ)) ≅ (afmc.obj (freeNerve β)).X p :=
  (afmc.obj (freeNerve β)).extendXIso ComplexShape.embeddingDownNat
    (ComplexShape.embeddingDownNat_f p)

/-- The comparison map in degree `-p` is the level-`p` map of the Čech nerves, up to the canonical
identifications `srcIso`. -/
theorem cechCmp_f {X X' Y Y' : LightCondSet.{0}} (β : X ⟶ Y) (β' : X' ⟶ Y')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (huv : u ≫ β = β' ≫ v) (p : ℕ) :
    (cechCmp β β' u v huv).f (-(p : ℤ)) =
      (srcIso β' p).hom ≫ (free ℤ).map (levelMap β β' u v huv p) ≫ (srcIso β p).inv := by
  rw [HomologicalComplex.extendMap_f (afmc.map (freeNerveMap β β' u v huv))
    ComplexShape.embeddingDownNat (ComplexShape.embeddingDownNat_f p)]
  have hcomp : (afmc.map (freeNerveMap β β' u v huv)).f p =
      (free ℤ).map (levelMap β β' u v huv p) :=
    AlgebraicTopology.AlternatingFaceMapComplex.map_f (freeNerveMap β β' u v huv) p
  rw [hcomp]

/-- The Čech complex vanishes in positive degrees. -/
theorem isZero_cechCpx_X_of_pos {X Y : LightCondSet.{0}} (β : X ⟶ Y) {q : ℤ} (hq : 0 < q) :
    IsZero ((cechCpx β).X q) := by
  refine HomologicalComplex.isZero_extend_X (afmc.obj (freeNerve β))
    ComplexShape.embeddingDownNat q ?_
  intro i hi
  rw [ComplexShape.embeddingDownNat_f] at hi
  omega

/-! ## Solid-equivalences and conjugation by isomorphisms -/

/-- `SolidEquiv` is invariant under conjugating a morphism by isomorphisms. -/
theorem solidEquiv_conj {A A' B B' : DLightCondAb} (f : A ⟶ B) (g : A' ⟶ B')
    (i : A' ≅ A) (j : B' ≅ B) (h : g = i.hom ≫ f ≫ j.inv) :
    SolidEquiv f ↔ SolidEquiv g := by
  haveI := i.isIso_hom
  haveI := j.isIso_inv
  constructor
  · intro hf
    rw [h]
    exact Work.TOOLKIT.solidEquiv_comp i.hom (f ≫ j.inv)
      (Work.TOOLKIT.solidEquiv_of_iso i.hom inferInstance)
      (Work.TOOLKIT.solidEquiv_comp f j.inv hf
        (Work.TOOLKIT.solidEquiv_of_iso j.inv inferInstance))
  · intro hg
    rw [h] at hg
    exact Work.TOOLKIT.solidEquiv_of_comp_right f j.inv
      (Work.TOOLKIT.solidEquiv_of_iso j.inv inferInstance)
      (Work.TOOLKIT.solidEquiv_of_comp_left i.hom (f ≫ j.inv)
        (Work.TOOLKIT.solidEquiv_of_iso i.hom inferInstance) hg)

/-! ## The levelwise comparison of the Čech complexes -/

/-- **Levelwise comparison of the Čech complexes.**  If the level-`p` maps of the Čech nerves are
solid-equivalences for all `p`, then the induced map of Čech complexes is a solid-equivalence. -/
theorem solidEquiv_cechCmp {X X' Y Y' : LightCondSet.{0}} (β : X ⟶ Y) (β' : X' ⟶ Y')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (huv : u ≫ β = β' ≫ v)
    (hlev : ∀ p : ℕ, SolidEquiv
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        ((free ℤ).map (levelMap β β' u v huv p)))) :
    SolidEquiv (DerivedCategory.Q.map (cechCmp β β' u v huv)) := by
  refine Work.TOOLKIT.solidEquiv_levelwise (cechCpx β') (cechCpx β) (cechCmp β β' u v huv)
    (fun q hq => isZero_cechCpx_X_of_pos β' hq)
    (fun q hq => isZero_cechCpx_X_of_pos β hq) ?_
  intro q
  by_cases hq : 0 < q
  · exact Work.TOOLKIT.solidEquiv_of_iso _ (IsZero.isIso
      (Functor.map_isZero _ (isZero_cechCpx_X_of_pos β' hq))
      (Functor.map_isZero _ (isZero_cechCpx_X_of_pos β hq)) _)
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, q = -(p : ℤ) := ⟨(-q).toNat, by omega⟩
    refine (solidEquiv_conj
      ((DerivedCategory.singleFunctor LightCondAb 0).map ((free ℤ).map (levelMap β β' u v huv p)))
      ((DerivedCategory.singleFunctor LightCondAb 0).map ((cechCmp β β' u v huv).f (-(p : ℤ))))
      ((DerivedCategory.singleFunctor LightCondAb 0).mapIso (srcIso β' p))
      ((DerivedCategory.singleFunctor LightCondAb 0).mapIso (srcIso β p)) ?_).mp (hlev p)
    rw [cechCmp_f, Functor.map_comp, Functor.map_comp]
    simp only [Functor.mapIso_hom, Functor.mapIso_inv]

/-! ## Descent for the Čech complex -/

/-- The chain-level augmentation is a quasi-isomorphism as soon as its degree-`0` homology map is
an isomorphism (the degree-`0` statement) and the Čech complex is acyclic in positive degrees. -/
theorem quasiIso_cechEps_of {X Y : LightCondSet.{0}} (β : X ⟶ Y)
    (h0 : IsIso (HomologicalComplex.homologyMap (cechEps β) 0))
    (hh : ∀ n : ℕ, IsZero ((afmc.obj (freeNerve β)).homology (n + 1))) :
    QuasiIso (cechEps β) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  match i with
  | 0 => exact h0
  | (n + 1) =>
      refine IsZero.isIso ?_ ?_ _
      · exact hh n
      · exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.down ℕ) 0
          ((free ℤ).obj Y) (n + 1) (Nat.succ_ne_zero n)

/-- The cochain-level augmentation of the Čech complex is a quasi-isomorphism, from the two
acyclicity inputs. -/
theorem quasiIso_cechAug_of {X Y : LightCondSet.{0}} (β : X ⟶ Y)
    (h0 : IsIso (HomologicalComplex.homologyMap (cechEps β) 0))
    (hh : ∀ n : ℕ, IsZero ((afmc.obj (freeNerve β)).homology (n + 1))) :
    QuasiIso (cechAug β) := by
  have hε : QuasiIso (cechEps β) := quasiIso_cechEps_of β h0 hh
  have hmap : QuasiIso (HomologicalComplex.extendMap (cechEps β)
      ComplexShape.embeddingDownNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff (cechEps β) ComplexShape.embeddingDownNat).mpr hε
  have hiso : QuasiIso (eiso ((free ℤ).obj Y)).hom := inferInstance
  rw [cechAug]
  exact (HomologicalComplex.quasiIso LightCondAb (ComplexShape.up ℤ)).comp_mem _ _ hmap hiso

/-- A quasi-isomorphism of cochain complexes is a solid-equivalence. -/
theorem solidEquiv_of_quasiIso {K L : CochainComplex LightCondAb ℤ} (f : K ⟶ L)
    (hf : QuasiIso f) : SolidEquiv (DerivedCategory.Q.map f) :=
  Work.TOOLKIT.solidEquiv_of_iso _
    ((DerivedCategory.isIso_Q_map_iff_quasiIso (C := LightCondAb) f).mpr hf)

/-- **Descent input.**  The augmentation of the Čech complex of an epimorphism is a
solid-equivalence. -/
theorem solidEquiv_cechAug_of {X Y : LightCondSet.{0}} (β : X ⟶ Y)
    (h0 : IsIso (HomologicalComplex.homologyMap (cechEps β) 0))
    (hh : ∀ n : ℕ, IsZero ((afmc.obj (freeNerve β)).homology (n + 1))) :
    SolidEquiv (DerivedCategory.Q.map (cechAug β)) :=
  solidEquiv_of_quasiIso _ (quasiIso_cechAug_of β h0 hh)

/-! ## The naturality square -/

/-- Naturality of the augmentation: the square comparing the augmentations of two Čech complexes
commutes, so that the induced map on the targets is the map induced on the spaces.

The input `hnat` is the naturality of `HomologicalComplex.extendSingleIso` in the object (a missing
Mathlib lemma, proved separately). -/
theorem cechAug_naturality {X X' Y Y' : LightCondSet.{0}} (β : X ⟶ Y) (β' : X' ⟶ Y')
    (u : X' ⟶ X) (v : Y' ⟶ Y) (huv : u ≫ β = β' ≫ v)
    (hnat : ∀ {A B : LightCondAb} (g : A ⟶ B),
      HomologicalComplex.extendMap ((ChainComplex.single₀ LightCondAb).map g)
          ComplexShape.embeddingDownNat ≫ (eiso B).hom =
        (eiso A).hom ≫
          (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).map g) :
    cechCmp β β' u v huv ≫ cechAug β = cechAug β' ≫
      (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).map ((free ℤ).map v) := by
  -- the chain-level square, from the naturality of the augmentation of the augmented Čech nerve
  have hsq : afmc.map (freeNerveMap β β' u v huv) ≫ cechEps β =
      cechEps β' ≫ (ChainComplex.single₀ LightCondAb).map ((free ℤ).map v) := by
    let A' := (SimplicialObject.Augmented.whiskeringObj _ LightCondAb (free ℤ)).map
      (Arrow.mapAugmentedCechNerve
        (Arrow.homMk (f := Arrow.mk β') (g := Arrow.mk β) u v huv))
    have h := AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality A'
    have hleft : (SimplicialObject.Augmented.drop ⋙ afmc).map A' =
        afmc.map (freeNerveMap β β' u v huv) := rfl
    have hright : (SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ LightCondAb).map A' =
        (ChainComplex.single₀ LightCondAb).map ((free ℤ).map v) := rfl
    rw [hleft, hright] at h
    exact h
  have hmap := congrArg (fun ψ => HomologicalComplex.extendMap ψ ComplexShape.embeddingDownNat) hsq
  rw [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_comp] at hmap
  calc cechCmp β β' u v huv ≫ cechAug β
      = (HomologicalComplex.extendMap (afmc.map (freeNerveMap β β' u v huv))
            ComplexShape.embeddingDownNat ≫
          HomologicalComplex.extendMap (cechEps β) ComplexShape.embeddingDownNat) ≫
          (eiso ((free ℤ).obj Y)).hom := by
        simp only [cechCmp, cechAug, ← Category.assoc]
    _ = (HomologicalComplex.extendMap (cechEps β') ComplexShape.embeddingDownNat ≫
          HomologicalComplex.extendMap ((ChainComplex.single₀ LightCondAb).map
            ((free ℤ).map v)) ComplexShape.embeddingDownNat) ≫
          (eiso ((free ℤ).obj Y)).hom := by rw [hmap]
    _ = HomologicalComplex.extendMap (cechEps β') ComplexShape.embeddingDownNat ≫
          (HomologicalComplex.extendMap ((ChainComplex.single₀ LightCondAb).map
            ((free ℤ).map v)) ComplexShape.embeddingDownNat ≫
            (eiso ((free ℤ).obj Y)).hom) := by simp only [Category.assoc]
    _ = HomologicalComplex.extendMap (cechEps β') ComplexShape.embeddingDownNat ≫
          ((eiso ((free ℤ).obj Y')).hom ≫
            (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).map
              ((free ℤ).map v)) := by rw [hnat ((free ℤ).map v)]
    _ = cechAug β' ≫
          (HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) 0).map
            ((free ℤ).map v) := by
        simp only [cechAug, Category.assoc]

end Work.ANALYTIC.CechGen
