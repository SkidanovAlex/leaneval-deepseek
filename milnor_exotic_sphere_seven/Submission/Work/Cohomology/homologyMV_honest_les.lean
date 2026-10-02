import Mathlib
import Submission.Work.Cohomology.pd_glue_defs
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.smallChains_homology_iso
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.homology_biprod_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The honest Mayer–Vietoris long exact sequence in singular homology

Let `X` be a topological space and `U, V ⊆ X` open subsets with `U ∪ V = X`.  The
Mayer–Vietoris short exact sequence of chain complexes

`0 ⟶ C_*(U ∩ V) ⟶ C_*(U) ⊞ C_*(V) ⟶ C^{U,V}_*(X) ⟶ 0`

(`Work.Cohomology.mvShort_shortExact`) together with the small-chains theorem
(`Work.Cohomology.smallIso`, identifying `H_*(C^{U,V}_*(X))` with the singular homology `H_*(X)`)
produces the long exact sequence

`⋯ ⟶ H_m(U ∩ V) ⟶ H_m(U) ⊞ H_m(V) ⟶ H_m(X) --δ--> H_{m-1}(U ∩ V) ⟶ ⋯`

The point of this file is to state and prove the *honest* form of this sequence, in the
vocabulary of `Work.Cohomology.pd_glue_defs`: the maps are morphisms between the honest homology
modules `pdHomInter`, `pdHomBiprod`, `pdHom` of *singular* chains, and the connecting maps are
required to be compatible with the structural maps `pdHomBiprodFst`, `pdHomBiprodInl`,
`pdHomMap`, `pdHomIncl` (so that the gluing `Good U → Good V → Good (U∩V) → Good (U∪V)` can
consume them).

The only point that is not literally the homology sequence of
`Work.Cohomology.mv_H_exactᵢ` is that

* the middle term of the short complex is the *homology of a biproduct* of chain complexes, which
  is identified with the biproduct of the homologies by the map `homMVBiprodIso` constructed below;
* the third term is the homology of the small chains, identified with the singular homology of `X`
  by `smallIso`.

## Main results

* `mvBiprodIso_exists`, `homMVBiprodIso` and its four structure-map lemmas
  `homMVBiprodIso_fst/snd/inl/inr`;
* `homMVF`, `homMVG`, `homMVδ` — the three maps of the sequence;
* `homMVF_fst`, `homMVF_snd`, `homMVG_inl`, `homMVG_inr` — their compatibility with the
  structural maps of `pd_glue_defs`;
* `homMVFG`, `homMVGδ`, `homMVδF` — the three composites vanish;
* `homMV_exact₂`, `homMV_exact₃`, `homMV_exact₁` — exactness at the three terms;
* `homologyMV_honest_les` — the long exact sequence.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-! ## The inclusion of the chains of `V` into the small chains

This is the `V`-analogue of `Work.Cohomology.smallOfU_comp_smallToSing`. -/

theorem mvSmallOfV_comp_smallToSing {X : TopCat} (U V : Set X) :
    smallOfV U V ≫ smallToSing U V = inclChains X V := by
  have h : SSet.chainComplexMap (smallLiftV U V) (ModuleCat.of ℤ ℤ) ≫
      SSet.chainComplexMap (smallSubcomplex U V).ι (ModuleCat.of ℤ ℤ)
      = SSet.chainComplexMap (TopCat.toSSet.map (inclVX V)) (ModuleCat.of ℤ ℤ) := by
    rw [← Functor.map_comp]
    rw [show smallLiftV U V ≫ (smallSubcomplex U V).ι = TopCat.toSSet.map (inclVX V) from
      SSet.Subcomplex.lift_ι _ _]
  exact h

/-! ## The homology of a biproduct of chain complexes

The `k`-th homology of a biproduct of chain complexes is the biproduct of the homologies,
compatibly with all four structure maps.  (This is the `ChainComplex` version of
`Work.Cohomology.homology_biprod_iso`; we record all four compatibilities at once, since the
honest Mayer–Vietoris sequence needs both the projections and the inclusions.) -/

theorem mvBiprodIso_exists (C D : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    ∃ e : (C ⊞ D).homology k ≅ C.homology k ⊞ D.homology k,
      (e.hom ≫ (biprod.fst : C.homology k ⊞ D.homology k ⟶ C.homology k)
          = HomologicalComplex.homologyMap (biprod.fst : C ⊞ D ⟶ C) k) ∧
      (e.hom ≫ (biprod.snd : C.homology k ⊞ D.homology k ⟶ D.homology k)
          = HomologicalComplex.homologyMap (biprod.snd : C ⊞ D ⟶ D) k) ∧
      ((biprod.inl : C.homology k ⟶ C.homology k ⊞ D.homology k) ≫ e.inv
          = HomologicalComplex.homologyMap (biprod.inl : C ⟶ C ⊞ D) k) ∧
      ((biprod.inr : D.homology k ⟶ C.homology k ⊞ D.homology k) ≫ e.inv
          = HomologicalComplex.homologyMap (biprod.inr : D ⟶ C ⊞ D) k) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k
  haveI : PreservesBinaryBiproduct C D F := preservesBinaryBiproduct_of_preservesBiproduct F C D
  refine ⟨F.mapBiprod C D, ?_, ?_, ?_, ?_⟩
  · erw [Functor.mapBiprod_hom, biprod.lift_fst]; rfl
  · erw [Functor.mapBiprod_hom, biprod.lift_snd]; rfl
  · erw [Functor.mapBiprod_inv, biprod.inl_desc]; rfl
  · erw [Functor.mapBiprod_inv, biprod.inr_desc]; rfl

/-- The chosen identification of the homology of the biproduct of the singular chains of `U` and
`V` with the biproduct of the homologies. -/
noncomputable def homMVBiprodIso (X : TopCat) (U V : Set X) (m : ℕ) :
    HBiprod U V m ≅ pdHomBiprod X U V m :=
  (mvBiprodIso_exists (singularChains ℤ (TopCat.of U)) (singularChains ℤ (TopCat.of V)) m).choose

/-- The first projection of the biproduct of homologies corresponds to the projection of the
biproduct of chain complexes. -/
theorem homMVBiprodIso_fst (X : TopCat) (U V : Set X) (m : ℕ) :
    (homMVBiprodIso X U V m).hom ≫ (biprod.fst : pdHomBiprod X U V m ⟶ pdHomSub X U m)
      = HomologicalComplex.homologyMap
          (biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
            singularChains ℤ (TopCat.of U)) m :=
  (mvBiprodIso_exists (singularChains ℤ (TopCat.of U)) (singularChains ℤ (TopCat.of V))
    m).choose_spec.1

/-- The second projection of the biproduct of homologies corresponds to the projection of the
biproduct of chain complexes. -/
theorem homMVBiprodIso_snd (X : TopCat) (U V : Set X) (m : ℕ) :
    (homMVBiprodIso X U V m).hom ≫ (biprod.snd : pdHomBiprod X U V m ⟶ pdHomSub X V m)
      = HomologicalComplex.homologyMap
          (biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
            singularChains ℤ (TopCat.of V)) m :=
  (mvBiprodIso_exists (singularChains ℤ (TopCat.of U)) (singularChains ℤ (TopCat.of V))
    m).choose_spec.2.1

/-- The first inclusion into the biproduct of homologies corresponds to the inclusion of the
biproduct of chain complexes. -/
theorem homMVBiprodIso_inl (X : TopCat) (U V : Set X) (m : ℕ) :
    (biprod.inl : pdHomSub X U m ⟶ pdHomBiprod X U V m) ≫ (homMVBiprodIso X U V m).inv
      = HomologicalComplex.homologyMap
          (biprod.inl : singularChains ℤ (TopCat.of U) ⟶
            singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)) m :=
  (mvBiprodIso_exists (singularChains ℤ (TopCat.of U)) (singularChains ℤ (TopCat.of V))
    m).choose_spec.2.2.1

/-- The second inclusion into the biproduct of homologies corresponds to the inclusion of the
biproduct of chain complexes. -/
theorem homMVBiprodIso_inr (X : TopCat) (U V : Set X) (m : ℕ) :
    (biprod.inr : pdHomSub X V m ⟶ pdHomBiprod X U V m) ≫ (homMVBiprodIso X U V m).inv
      = HomologicalComplex.homologyMap
          (biprod.inr : singularChains ℤ (TopCat.of V) ⟶
            singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)) m :=
  (mvBiprodIso_exists (singularChains ℤ (TopCat.of U)) (singularChains ℤ (TopCat.of V))
    m).choose_spec.2.2.2

/-! ## The three maps of the sequence -/

/-- The first map `H_m(U ∩ V) ⟶ H_m(U) ⊞ H_m(V)` of the honest Mayer–Vietoris sequence. -/
noncomputable def homMVF (X : TopCat) (U V : Set X) (m : ℕ) :
    pdHomInter X U V m ⟶ pdHomBiprod X U V m :=
  HomologicalComplex.homologyMap (mvLeft U V) m ≫ (homMVBiprodIso X U V m).hom

/-- The second map `H_m(U) ⊞ H_m(V) ⟶ H_m(X)` of the honest Mayer–Vietoris sequence. -/
noncomputable def homMVG (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ) : pdHomBiprod X U V m ⟶ pdHom X m :=
  (homMVBiprodIso X U V m).inv ≫ HomologicalComplex.homologyMap (mvRight U V) m ≫
    (smallIso U V hU hV hcov m).hom

/-- The connecting map `H_{m+1}(X) ⟶ H_m(U ∩ V)` of the honest Mayer–Vietoris sequence. -/
noncomputable def homMVδ (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ) : pdHom X (m + 1) ⟶ pdHomInter X U V m :=
  (smallIso U V hU hV hcov (m + 1)).inv ≫ mvδ U V m

/-! ## Compatibility with the structural maps -/

/-- The first component of `F` is the map induced by the inclusion `U ∩ V ⊆ U`. -/
theorem homMVF_fst (X : TopCat) (U V : Set X) (m : ℕ) :
    homMVF X U V m ≫ pdHomBiprodFst X U V m
      = pdHomMap X U (U ∩ V) Set.inter_subset_left m := by
  rw [homMVF, pdHomBiprodFst, Category.assoc, homMVBiprodIso_fst,
    ← HomologicalComplex.homologyMap_comp, mvLeft, biprod.lift_fst]
  rw [show inclUVU U V = pdIncl U (U ∩ V) Set.inter_subset_left from by ext x; rfl]
  rw [pdHomMap]
  rfl

/-- The second component of `F` is the map induced by the inclusion `U ∩ V ⊆ V`. -/
theorem homMVF_snd (X : TopCat) (U V : Set X) (m : ℕ) :
    homMVF X U V m ≫ pdHomBiprodSnd X U V m
      = pdHomMap X V (U ∩ V) Set.inter_subset_right m := by
  rw [homMVF, pdHomBiprodSnd, Category.assoc, homMVBiprodIso_snd,
    ← HomologicalComplex.homologyMap_comp, mvLeft, biprod.lift_snd]
  rw [show inclUVV U V = pdIncl V (U ∩ V) Set.inter_subset_right from by ext x; rfl]
  rw [pdHomMap]
  rfl

/-- The small-chains isomorphism is the map induced by the inclusion of the small chains. -/
theorem smallIso_hom_eq (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ) :
    (smallIso U V hU hV hcov m).hom = HomologicalComplex.homologyMap (smallToSing U V) m := by
  rw [smallIso, asIso_hom]

/-- The `U`-component of `G` is the map induced by the inclusion `U ⊆ X`. -/
theorem homMVG_inl (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ) :
    pdHomBiprodInl X U V m ≫ homMVG X U V hU hV hcov m = pdHomIncl X U m := by
  rw [pdHomBiprodInl, homMVG, ← Category.assoc, homMVBiprodIso_inl, ← Category.assoc,
    ← HomologicalComplex.homologyMap_comp, mvRight, biprod.inl_desc]
  rw [smallIso_hom_eq, ← HomologicalComplex.homologyMap_comp, smallOfU_comp_smallToSing]
  rfl

/-- The `V`-component of `G` is the negative of the map induced by the inclusion `V ⊆ X`. -/
theorem homMVG_inr (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ) :
    pdHomBiprodInr X U V m ≫ homMVG X U V hU hV hcov m = pdNeg (pdHomIncl X V m) := by
  rw [pdHomBiprodInr, homMVG, ← Category.assoc, homMVBiprodIso_inr, ← Category.assoc,
    ← HomologicalComplex.homologyMap_comp, mvRight, biprod.inr_desc]
  rw [smallIso_hom_eq, ← HomologicalComplex.homologyMap_comp, Preadditive.neg_comp,
    HomologicalComplex.homologyMap_neg, mvSmallOfV_comp_smallToSing]
  rfl

/-! ## The three composites vanish -/

/-- `F_m ≫ G_m = 0`. -/
theorem homMVFG (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ) :
    homMVF X U V m ≫ homMVG X U V hU hV hcov m = 0 := by
  rw [homMVF, homMVG]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← HomologicalComplex.homologyMap_comp, mvComp,
    HomologicalComplex.homologyMap_zero, zero_comp]

/-- `G_{m+1} ≫ δ_m = 0`. -/
theorem homMVGδ (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ) :
    homMVG X U V hU hV hcov (m + 1) ≫ homMVδ X U V hU hV hcov m = 0 := by
  rw [homMVG, homMVδ]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc, mv_comp_δ, comp_zero]

/-- `δ_m ≫ F_m = 0`. -/
theorem homMVδF (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ) :
    homMVδ X U V hU hV hcov m ≫ homMVF X U V m = 0 := by
  rw [homMVδ, homMVF]
  simp only [Category.assoc]
  rw [← Category.assoc (mvδ U V m) (HomologicalComplex.homologyMap (mvLeft U V) m)
      (homMVBiprodIso X U V m).hom, mvδ_comp, zero_comp, comp_zero]

/-! ## Exactness -/

/-- Exactness at `H_m(U) ⊞ H_m(V)`. -/
theorem homMV_exact₂ (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ) :
    (ShortComplex.mk (homMVF X U V m) (homMVG X U V hU hV hcov m)
      (homMVFG X U V hU hV hcov m)).Exact := by
  let S₁ : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk (HomologicalComplex.homologyMap (mvLeft U V) m)
      (HomologicalComplex.homologyMap (mvRight U V) m)
      (by rw [← HomologicalComplex.homologyMap_comp, mvComp,
        HomologicalComplex.homologyMap_zero])
  have hS₁ : S₁.Exact := mv_H_exact₂ U V m
  have hw₁ : (Iso.refl _).hom ≫ homMVF X U V m
      = HomologicalComplex.homologyMap (mvLeft U V) m ≫ (homMVBiprodIso X U V m).hom := by
    rw [Iso.refl_hom, Category.id_comp]; rfl
  have hw₂ : (homMVBiprodIso X U V m).hom ≫ homMVG X U V hU hV hcov m
      = HomologicalComplex.homologyMap (mvRight U V) m ≫ (smallIso U V hU hV hcov m).hom := by
    rw [homMVG, Iso.hom_inv_id_assoc]
  let S₂ : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk (homMVF X U V m) (homMVG X U V hU hV hcov m) (homMVFG X U V hU hV hcov m)
  let φ : S₁ ≅ S₂ :=
    ShortComplex.isoMk (Iso.refl _) (homMVBiprodIso X U V m) (smallIso U V hU hV hcov m) hw₁ hw₂
  exact ShortComplex.exact_of_iso φ hS₁

/-- Exactness at `H_{m+1}(X)`. -/
theorem homMV_exact₃ (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ) :
    (ShortComplex.mk (homMVG X U V hU hV hcov (m + 1)) (homMVδ X U V hU hV hcov m)
      (homMVGδ X U V hU hV hcov m)).Exact := by
  let S₁ : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk (HomologicalComplex.homologyMap (mvRight U V) (m + 1)) (mvδ U V m)
      (mv_comp_δ U V m)
  have hS₁ : S₁.Exact := mv_H_exact₃ U V m
  have hw₁ : (homMVBiprodIso X U V (m + 1)).hom ≫ homMVG X U V hU hV hcov (m + 1)
      = HomologicalComplex.homologyMap (mvRight U V) (m + 1) ≫
          (smallIso U V hU hV hcov (m + 1)).hom := by
    rw [homMVG, Iso.hom_inv_id_assoc]
  have hw₂ : (smallIso U V hU hV hcov (m + 1)).hom ≫ homMVδ X U V hU hV hcov m
      = mvδ U V m ≫ (Iso.refl _).hom := by
    rw [homMVδ, Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]
  let S₂ : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk (homMVG X U V hU hV hcov (m + 1)) (homMVδ X U V hU hV hcov m)
      (homMVGδ X U V hU hV hcov m)
  let φ : S₁ ≅ S₂ :=
    ShortComplex.isoMk (homMVBiprodIso X U V (m + 1)) (smallIso U V hU hV hcov (m + 1))
      (Iso.refl _) hw₁ hw₂
  exact ShortComplex.exact_of_iso φ hS₁

/-- Exactness at `H_m(U ∩ V)`. -/
theorem homMV_exact₁ (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (m : ℕ) :
    (ShortComplex.mk (homMVδ X U V hU hV hcov m) (homMVF X U V m)
      (homMVδF X U V hU hV hcov m)).Exact := by
  let S₁ : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk (mvδ U V m) (HomologicalComplex.homologyMap (mvLeft U V) m)
      (mvδ_comp U V m)
  have hS₁ : S₁.Exact := mv_H_exact₁ U V m
  have hw₁ : (smallIso U V hU hV hcov (m + 1)).hom ≫ homMVδ X U V hU hV hcov m
      = mvδ U V m ≫ (Iso.refl _).hom := by
    rw [homMVδ, Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]
  have hw₂ : (Iso.refl _).hom ≫ homMVF X U V m
      = HomologicalComplex.homologyMap (mvLeft U V) m ≫ (homMVBiprodIso X U V m).hom := by
    rw [Iso.refl_hom, Category.id_comp]; rfl
  let S₂ : ShortComplex (ModuleCat ℤ) :=
    ShortComplex.mk (homMVδ X U V hU hV hcov m) (homMVF X U V m) (homMVδF X U V hU hV hcov m)
  let φ : S₁ ≅ S₂ :=
    ShortComplex.isoMk (smallIso U V hU hV hcov (m + 1)) (Iso.refl _) (homMVBiprodIso X U V m)
      hw₁ hw₂
  exact ShortComplex.exact_of_iso φ hS₁

/-! ## The long exact sequence -/

theorem homologyMV_honest_les (X : TopCat) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) :
    ∃ (F : ∀ m, Work.Cohomology.pdMor (Work.Cohomology.pdHomInter X U V m)
          (Work.Cohomology.pdHomBiprod X U V m))
      (G : ∀ m, Work.Cohomology.pdMor (Work.Cohomology.pdHomBiprod X U V m)
          (Work.Cohomology.pdHom X m))
      (δ : ∀ m, Work.Cohomology.pdMor (Work.Cohomology.pdHom X (m + 1))
          (Work.Cohomology.pdHomInter X U V m))
      (hFG : ∀ m, Work.Cohomology.pdComp (F m) (G m) = Work.Cohomology.pdZero _ _)
      (hGδ : ∀ m, Work.Cohomology.pdComp (G (m + 1)) (δ m) = Work.Cohomology.pdZero _ _)
      (hδF : ∀ m, Work.Cohomology.pdComp (δ m) (F m) = Work.Cohomology.pdZero _ _),
      (∀ m, Work.Cohomology.pdComp (F m) (Work.Cohomology.pdHomBiprodFst X U V m)
        = Work.Cohomology.pdHomMap X U (U ∩ V) Set.inter_subset_left m) ∧
      (∀ m, Work.Cohomology.pdComp (F m) (Work.Cohomology.pdHomBiprodSnd X U V m)
        = Work.Cohomology.pdHomMap X V (U ∩ V) Set.inter_subset_right m) ∧
      (∀ m, Work.Cohomology.pdComp (Work.Cohomology.pdHomBiprodInl X U V m) (G m)
        = Work.Cohomology.pdHomIncl X U m) ∧
      (∀ m, Work.Cohomology.pdComp (Work.Cohomology.pdHomBiprodInr X U V m) (G m)
        = Work.Cohomology.pdNeg (Work.Cohomology.pdHomIncl X V m)) ∧
      (∀ m, Work.Cohomology.pdExact (F m) (G m) (hFG m)) ∧
      (∀ m, Work.Cohomology.pdExact (G (m + 1)) (δ m) (hGδ m)) ∧
      (∀ m, Work.Cohomology.pdExact (δ m) (F m) (hδF m)) := by
  refine ⟨homMVF X U V, homMVG X U V hU hV hcov, homMVδ X U V hU hV hcov,
    fun m => homMVFG X U V hU hV hcov m,
    fun m => homMVGδ X U V hU hV hcov m,
    fun m => homMVδF X U V hU hV hcov m,
    fun m => homMVF_fst X U V m,
    fun m => homMVF_snd X U V m,
    fun m => homMVG_inl X U V hU hV hcov m,
    fun m => homMVG_inr X U V hU hV hcov m,
    fun m => homMV_exact₂ X U V hU hV hcov m,
    fun m => homMV_exact₃ X U V hU hV hcov m,
    fun m => homMV_exact₁ X U V hU hV hcov m⟩

end

end Work.Cohomology
