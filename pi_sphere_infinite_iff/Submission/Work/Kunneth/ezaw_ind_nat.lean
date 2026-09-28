import Mathlib
import Submission.Work.Kunneth.EZAWDefs
import Submission.Work.Kunneth.ezHom_d
import Submission.Work.Kunneth.EZHom2
import Submission.Work.Kunneth.tChain_hom_ext

/-!
# Naturality of `Ezaw = ezMap ≫ awMap` in the two variables

For simplicial sets `X, Y` the composite of the Eilenberg–Zilber shuffle map with the
Alexander–Whitney map,

`Ezaw X Y = ezMap X Y ≫ awMap X Y : tChain X Y ⟶ tChain X Y`,

is a natural transformation of the bifunctor `(X, Y) ↦ C_*(X) ⊗_ℤ C_*(Y)`.  Here `tChain X Y` is
`Work.Kunneth.tpC (sChain X) (sChain Y)` and `Work.Kunneth.ind f g` is the induced map
`tpMap (chainComplexMap f) (chainComplexMap g)`; the statement proved below is the naturality
square

`ind f g ≫ Ezaw X2 Y2 = Ezaw X Y ≫ ind f g`.

The two factors are natural separately:

* `ezaw_awMap_naturality` — `chainComplexMap (f ⊗ g) ≫ awMap X2 Y2 = awMap X Y ≫ ind f g`;  this
  reduces, on a generator `(σ, τ)` of `C_*(X ⊗ Y)`, to `ezaw_awGen_nat`, the statement that the front
  and back faces commute with the simplicial maps `f`, `g`;
* `ezaw_ezMap_naturality` — `ind f g ≫ ezMap X2 Y2 = ezMap X Y ≫ chainComplexMap (f ⊗ g)`;  on a
  shuffle generator this is `ezaw_ezGen_nat`, together with the transport `ezaw_chainComplexMap_eqToHom_apply`
  of a chain map along the degree identification `p + q = n` used in `ezGenN`.

Combining the two gives the theorem `ezaw_ind_nat`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## Auxiliary identity lemmas -/

/-- The component `(ind f g).f n` applied to an element, in terms of `tpMapLin`. -/
lemma ezaw_ind_apply {X X2 Y Y2 : SSet} (f : X ⟶ X2) (g : Y ⟶ Y2) (n : ℕ)
    (x : ↥((tChain X Y).X n)) :
    ModuleCat.Hom.hom ((ind f g).f n) x
      = tpMapLin (sChain X) (sChain X2) (sChain Y) (sChain Y2)
          (SSet.chainComplexMap f zz) (SSet.chainComplexMap g zz) n x := rfl

/-- A chain map commutes with the `eqToHom` transport of a change of degree, on elements. -/
lemma ezaw_chainComplexMap_eqToHom_apply {C D : ChainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D) {a b : ℕ}
    (h : a = b) (x : ↥(C.X a)) :
    ModuleCat.Hom.hom (φ.f b) (ModuleCat.Hom.hom (eqToHom (congrArg C.X h)) x)
      = ModuleCat.Hom.hom (eqToHom (congrArg D.X h)) (ModuleCat.Hom.hom (φ.f a) x) := by
  have hmor : eqToHom (congrArg C.X h) ≫ φ.f b = φ.f a ≫ eqToHom (congrArg D.X h) := by
    subst h
    simp
  have := congrArg (fun (g : C.X a ⟶ D.X b) => ModuleCat.Hom.hom g x) hmor
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this

/-! ## Naturality on generators -/

/-- **Naturality of the Alexander–Whitney chain on a generator.** -/
lemma ezaw_awGen_nat {X X2 Y Y2 : SSet} (f : X ⟶ X2) (g : Y ⟶ Y2) (n : ℕ) (z : (X ⊗ Y) _⦋n⦌) :
    tpMapLin (sChain X) (sChain X2) (sChain Y) (sChain Y2)
        (SSet.chainComplexMap f zz) (SSet.chainComplexMap g zz) n ((awGen X Y n z).hom 1)
      = (awGen X2 Y2 n
          ((MonoidalCategoryStruct.tensorHom f g).app (Opposite.op ⦋n⦌) z)).hom 1 := by
  rw [awGen_hom_one, awGen_hom_one, map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [tpMapLin_tmul]
  congr 1
  rw [EZHom.genCh_chainComplexMap, EZHom.genCh_chainComplexMap]
  rw [EZHom.tensorHom_fst, EZHom.tensorHom_snd, EZHom.frontFace_nat, EZHom.backFaceLE_nat]

/-- **Naturality of the Eilenberg–Zilber shuffle chain `ezGen` on a pair of generators.** -/
lemma ezaw_ezGen_nat {X X2 Y Y2 : SSet} (f : X ⟶ X2) (g : Y ⟶ Y2) (p q : ℕ)
    (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    ModuleCat.Hom.hom ((SSet.chainComplexMap (MonoidalCategoryStruct.tensorHom f g) zz).f (p+q))
        (Work.Cohomology.Crux33.ezGen p q X Y σ τ)
      = Work.Cohomology.Crux33.ezGen p q X2 Y2 (f.app (Opposite.op ⦋p⦌) σ)
          (g.app (Opposite.op ⦋q⦌) τ) := by
  rw [Work.Cohomology.Crux33.ezGen, Work.Cohomology.Crux33.ezGen, map_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [map_zsmul]
  congr 1
  rw [EZHom.genCh_chainComplexMap, EZHom.tensorHom_map_op]

/-! ## Naturality of the two factors -/

/-- **Naturality of the Alexander–Whitney chain map** `C_*(X ⊗ Y) ⟶ C_*(X) ⊗_ℤ C_*(Y)`. -/
lemma ezaw_awMap_naturality {X X2 Y Y2 : SSet} (f : X ⟶ X2) (g : Y ⟶ Y2) :
    SSet.chainComplexMap (MonoidalCategoryStruct.tensorHom f g) zz ≫ awMap X2 Y2
      = awMap X Y ≫ ind f g := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply SSet.chainComplex_hom_ext
  intro z
  apply EZHom.ModuleCat_zz_ext
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [awMap_f, awMap_f]
  rw [EZHom.genCh_chainComplexMap]
  rw [show (awHom X2 Y2 n).hom (genCh (sProd X2 Y2)
        ((MonoidalCategoryStruct.tensorHom f g).app (Opposite.op ⦋n⦌) z))
      = ((sProd X2 Y2).ιChainComplex ((MonoidalCategoryStruct.tensorHom f g).app
          (Opposite.op ⦋n⦌) z) ≫ awHom X2 Y2 n).hom 1 from
      EZHom.genCh_hom_apply n _ (awHom X2 Y2 n)]
  rw [awHom_gen]
  rw [← Category.assoc, awHom_gen X Y n z, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ezaw_ind_apply]
  rw [ezaw_awGen_nat]

/-- **Naturality of the Eilenberg–Zilber shuffle chain map** `C_*(X) ⊗_ℤ C_*(Y) ⟶ C_*(X ⊗ Y)`. -/
lemma ezaw_ezMap_naturality {X X2 Y Y2 : SSet} (f : X ⟶ X2) (g : Y ⟶ Y2) :
    ind f g ≫ ezMap X2 Y2
      = ezMap X Y ≫ SSet.chainComplexMap (MonoidalCategoryStruct.tensorHom f g) zz := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply tChain_hom_ext
  intro p q hpq σ τ
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ezMap_f, ezMap_f]
  rw [show (ind f g).f n = (tpMap (sChain X) (sChain X2) (sChain Y) (sChain Y2)
        (SSet.chainComplexMap f zz) (SSet.chainComplexMap g zz)).f n from rfl]
  rw [tpMap_tpLof, TensorProduct.map_tmul]
  rw [EZHom.genCh_chainComplexMap, EZHom.genCh_chainComplexMap]
  rw [EZHom.ezHom_tpLof_gen, EZHom.ezHom_tpLof_gen]
  rw [EZHom.ezGenN, EZHom.ezGenN]
  rw [ezaw_chainComplexMap_eqToHom_apply
    (SSet.chainComplexMap (MonoidalCategoryStruct.tensorHom f g) zz) hpq]
  rw [ezaw_ezGen_nat]

/-! ## The theorem -/

theorem ezaw_ind_nat {X Y X2 Y2 : SSet} (f : X ⟶ X2) (g : Y ⟶ Y2) :
    CategoryTheory.CategoryStruct.comp (Work.Kunneth.ind f g) (Work.Kunneth.Ezaw X2 Y2)
      = CategoryTheory.CategoryStruct.comp (Work.Kunneth.Ezaw X Y) (Work.Kunneth.ind f g) := by
  rw [Ezaw, Ezaw]
  rw [← Category.assoc]
  rw [ezaw_ezMap_naturality]
  rw [Category.assoc, ezaw_awMap_naturality]
  rw [Category.assoc]

end

end Work.Kunneth
