import Mathlib
import Submission.Work.Kunneth.Tensor
import Submission.Work.Kunneth.TensorDefs
import Submission.Work.Kunneth.tpD_comp_tpD

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Functoriality of the Koszul tensor product of chain complexes

`Work.Kunneth.tpMap f g : tpC C D ⟶ tpC C' D'` is the tensor product of two chain maps on the
Koszul tensor product `tpC` of `Submission/Work/Kunneth/Tensor.lean`.  This file provides the
value on summand generators (`tpMap_tpLof`, `tpMap_tpLof_tmul`), the compatibility with the
Koszul differential (`tpMapLin_d`), the functoriality (`tpMap_id`, `tpMap_comp`) needed by the
Eilenberg–Zilber `ezMap ≫ awMap ≃ 𝟙` argument.

The element-level version `tpMapLin` of the components is the workhorse: it is a plain
`ℤ`-linear map between the `DirectSum`s `tpX C D n`, so that no `ModuleCat`-instance issues
arise in the element computations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## The `ℤ`-linear components -/

/-- The `n`-th component of the tensor product of two chain maps, as a `ℤ`-linear map between
the underlying direct sums `tpX`. -/
def tpMapLin (C C' D D' : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ C') (g : D ⟶ D') (n : ℕ) :
    tpX C D n →ₗ[ℤ] tpX C' D' n :=
  DirectSum.toModule ℤ (tpIdx n) (tpX C' D' n)
    (fun pq => (tpLof C' D' n pq).comp (TensorProduct.map (f.f pq.1.1).hom (g.f pq.1.2).hom))

/-- The value of `tpMapLin` on a summand generator. -/
lemma tpMapLin_tpLof (C C' D D' : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ C') (g : D ⟶ D')
    (n : ℕ) (pq : tpIdx n) (z : tpSummand C D pq.1.1 pq.1.2) :
    tpMapLin C C' D D' f g n (tpLof C D n pq z)
      = tpLof C' D' n pq ((TensorProduct.map (f.f pq.1.1).hom (g.f pq.1.2).hom) z) := by
  rw [tpMapLin, DirectSum.toModule_lof]
  rfl

/-- The value of `tpMapLin` on a pure tensor of generators. -/
lemma tpMapLin_tmul (C C' D D' : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ C') (g : D ⟶ D')
    (n : ℕ) (pq : tpIdx n) (x : ↥(C.X pq.1.1)) (y : ↥(D.X pq.1.2)) :
    tpMapLin C C' D D' f g n (tpLof C D n pq (x ⊗ₜ[ℤ] y))
      = tpLof C' D' n pq ((f.f pq.1.1).hom x ⊗ₜ[ℤ] (g.f pq.1.2).hom y) := by
  rw [tpMapLin_tpLof, TensorProduct.map_tmul]

/-- A chain map translates the differential of a pair of elements: element-level form of
`HomologicalComplex.Hom.comm`. -/
lemma Hom_comm_apply {C C' : ChainComplex (ModuleCat ℤ) ℕ} (f : C ⟶ C') (i k : ℕ)
    (x : ↥(C.X i)) :
    (C'.d i k).hom ((f.f i).hom x) = (f.f k).hom ((C.d i k).hom x) := by
  have hc := congrArg (fun (φ : C.X i ⟶ C'.X k) => ModuleCat.Hom.hom φ x)
    (HomologicalComplex.Hom.comm f i k)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hc

/-- The component `tpMapLin` is compatible with the Koszul differentials. -/
theorem tpMapLin_d (C C' D D' : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ C') (g : D ⟶ D')
    (j : ℕ) :
    (tpD C' D' j) ∘ₗ tpMapLin C C' D D' f g (j + 1)
      = tpMapLin C C' D D' f g j ∘ₗ (tpD C D j) := by
  refine DirectSum.linearMap_ext ℤ (fun pq => ?_)
  apply TensorProduct.ext'
  intro x y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  change (tpD C' D' j) (tpMapLin C C' D D' f g (j + 1) (tpLof C D (j + 1) pq (x ⊗ₜ[ℤ] y)))
      = tpMapLin C C' D D' f g j ((tpD C D j) (tpLof C D (j + 1) pq (x ⊗ₜ[ℤ] y)))
  rw [tpMapLin_tpLof, TensorProduct.map_tmul, tpD_lof_tmul]
  rw [tpD_lof_tmul, map_add]
  congr 1
  · split_ifs with hp
    · rw [tpMapLin_tpLof, TensorProduct.map_tmul]
      congr 1
      congr 1
      exact Hom_comm_apply f (pq.1.1) (pq.1.1 - 1) x
    · rw [map_zero]
  · split_ifs with hq
    · rw [map_zsmul]
      congr 1
      rw [tpMapLin_tpLof, TensorProduct.map_tmul]
      congr 1
      congr 1
      exact Hom_comm_apply g (pq.1.2) (pq.1.2 - 1) y
    · rw [map_zero]

/-! ## The tensor product of two chain maps -/

/-- **The tensor product of two chain maps** on the Koszul tensor product: on the `(p,q)`-summand
it is `f_p ⊗ g_q`. -/
def tpMap (C C' D D' : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ C') (g : D ⟶ D') :
    tpC C D ⟶ tpC C' D' where
  f n := ModuleCat.ofHom (tpMapLin C C' D D' f g n)
  comm' := by
    rintro i j (hij : j + 1 = i)
    subst hij
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, tpC_d, tpC_d, ModuleCat.hom_ofHom,
      ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
    exact tpMapLin_d C C' D D' f g j

@[simp]
theorem tpMap_f (C C' D D' : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ C') (g : D ⟶ D')
    (n : ℕ) : (tpMap C C' D D' f g).f n = ModuleCat.ofHom (tpMapLin C C' D D' f g n) := rfl

/-- The value of `tpMap` on a summand generator. -/
theorem tpMap_tpLof (X X' Y Y' : ChainComplex (ModuleCat ℤ) ℕ) (f : X ⟶ X') (g : Y ⟶ Y')
    (n : ℕ) (pq : tpIdx n) (z : tpSummand X Y pq.1.1 pq.1.2) :
    (tpMap X X' Y Y' f g).f n (tpLof X Y n pq z)
      = tpLof X' Y' n pq ((TensorProduct.map (f.f pq.1.1).hom (g.f pq.1.2).hom) z) := by
  rw [tpMap_f]
  exact tpMapLin_tpLof X X' Y Y' f g n pq z

/-- The value of `tpMap` on a pure tensor of generators. -/
theorem tpMap_tmul (X X' Y Y' : ChainComplex (ModuleCat ℤ) ℕ) (f : X ⟶ X') (g : Y ⟶ Y')
    (n : ℕ) (pq : tpIdx n) (x : ↥(X.X pq.1.1)) (y : ↥(Y.X pq.1.2)) :
    (tpMap X X' Y Y' f g).f n (tpLof X Y n pq (x ⊗ₜ[ℤ] y))
      = tpLof X' Y' n pq ((f.f pq.1.1).hom x ⊗ₜ[ℤ] (g.f pq.1.2).hom y) := by
  rw [tpMap_f]
  exact tpMapLin_tmul X X' Y Y' f g n pq x y

theorem tpMap_id (C D : ChainComplex (ModuleCat ℤ) ℕ) :
    tpMap C C D D (𝟙 C) (𝟙 D) = 𝟙 (tpC C D) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [tpMap_f, HomologicalComplex.id_f]
  change ModuleCat.ofHom (tpMapLin C C D D (𝟙 C) (𝟙 D) n)
      = 𝟙 (ModuleCat.of ℤ (tpX C D n))
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id]
  apply DirectSum.linearMap_ext ℤ
  intro pq
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  change tpMapLin C C D D (𝟙 C) (𝟙 D) n (tpLof C D n pq (x ⊗ₜ[ℤ] y))
      = tpLof C D n pq (x ⊗ₜ[ℤ] y)
  rw [tpMapLin_tmul]
  simp only [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]

theorem tpMap_comp (C C' C'' D D' D'' : ChainComplex (ModuleCat ℤ) ℕ)
    (f : C ⟶ C') (g : D ⟶ D') (f' : C' ⟶ C'') (g' : D' ⟶ D'') :
    tpMap C C' D D' f g ≫ tpMap C' C'' D' D'' f' g'
      = tpMap C C'' D D'' (f ≫ f') (g ≫ g') := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, tpMap_f, tpMap_f, tpMap_f]
  rw [← ModuleCat.ofHom_comp]
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_ofHom]
  apply DirectSum.linearMap_ext ℤ
  intro pq
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply]
  change tpMapLin C' C'' D' D'' f' g' n
        (tpMapLin C C' D D' f g n (tpLof C D n pq (x ⊗ₜ[ℤ] y)))
      = tpMapLin C C'' D D'' (f ≫ f') (g ≫ g') n (tpLof C D n pq (x ⊗ₜ[ℤ] y))
  rw [tpMapLin_tmul, tpMapLin_tmul, tpMapLin_tmul]
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]

end

end Work.Kunneth
