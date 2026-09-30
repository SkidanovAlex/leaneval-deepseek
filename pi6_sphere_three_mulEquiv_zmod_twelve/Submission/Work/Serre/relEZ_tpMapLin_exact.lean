import Mathlib
import Submission.Work.Kunneth.Chapter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Exactness of the tensor product of a chain map with a degreewise flat complex

This file proves `Work.Serre.relEZ_tpMapLin_exact`: for a chain complex `C` of `ℤ`-modules whose
components are flat (`hC`), the `n`-th component of the tensor product (Koszul) of the pair

  `A --f--> B --cokernel.π f--> cokernel f`

stays exact after tensoring with `C`:

`Function.Exact (tpMapLin C C A B 𝟙 f n) (tpMapLin C C B (cokernel f) 𝟙 (cokernel.π f) n)`.

The proof has three ingredients, all of them recorded here:

* **Direct sums.**  `tpX C D n = ⨁_{p+q=n} C_p ⊗ D_q` and `tpMapLin` is the direct sum of the maps
  `id ⊗ (·)`.  A finite direct sum of exact pairs of linear maps is exact
  (`Work.Serre.functionExact_dsMap`), with the structure-map reconstruction
  `Work.Serre.sum_lof_component` and the component formula `Work.Serre.component_dsMap` as the two
  element-level inputs.
* **Finiteness of the bidegree index.**  `tpIdx n` is finite (`Work.Kunneth.tpIdx.instFintype`),
  which is what makes the reconstruction available.
* **Flatness.**  For fixed `p + q = n`, the pair `(f_q, (cokernel.π f)_q)` is exact degreewise
  (`Work.Serre.functionExact_cokernelπ`, from the canonicality of the cokernel in the functor
  category), and tensoring an exact pair with the flat module `C_p` preserves exactness
  (`Module.Flat.lTensor_exact`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Serre

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

open Work.Kunneth

/-! ## 1. Direct sums of exact pairs of linear maps -/

/-- The structure maps of a finite direct sum reconstruct its elements:
`∑ i, lof i (x i) = x`. -/
theorem sum_lof_component {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module ℤ (M i)] (x : DirectSum ι M) :
    ∑ i, DirectSum.lof ℤ ι M i (x i) = x := by
  apply DirectSum.ext
  intro k
  rw [← DirectSum.coeFnLinearMap_apply (R := ℤ)
    (v := ∑ i, DirectSum.lof ℤ ι M i (x i))]
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single k]
  · simp only [DirectSum.coeFnLinearMap_apply, DirectSum.lof_apply]
  · intro j _ hj
    change DirectSum.component ℤ ι M k (DirectSum.lof ℤ ι M j (x j)) = 0
    rw [DirectSum.component.of]
    simp [hj]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **The direct sum of a family of linear maps**, `⨁ i, f i : ⨁ i, M i → ⨁ i, N i`. -/
def dsMap {ι : Type*} [DecidableEq ι] {M N : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module ℤ (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module ℤ (N i)]
    (f : ∀ i, M i →ₗ[ℤ] N i) : (DirectSum ι M) →ₗ[ℤ] (DirectSum ι N) :=
  DirectSum.toModule ℤ ι (DirectSum ι N) fun i => (DirectSum.lof ℤ ι N i).comp (f i)

/-- The value of a direct sum of linear maps on a structure-map generator. -/
theorem dsMap_lof {ι : Type*} [DecidableEq ι] {M N : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module ℤ (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module ℤ (N i)]
    (f : ∀ i, M i →ₗ[ℤ] N i) (i : ι) (x : M i) :
    dsMap f (DirectSum.lof ℤ ι M i x) = DirectSum.lof ℤ ι N i (f i x) := by
  rw [dsMap, DirectSum.toModule_lof]
  rfl

/-- The components of a direct sum of linear maps: the `i`-th component of `dsMap f x` is
`f i` applied to the `i`-th component of `x`. -/
theorem component_dsMap {ι : Type*} [DecidableEq ι] {M N : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module ℤ (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module ℤ (N i)]
    (f : ∀ i, M i →ₗ[ℤ] N i) (i : ι) :
    (DirectSum.component ℤ ι N i) ∘ₗ (dsMap f)
      = (f i) ∘ₗ (DirectSum.component ℤ ι M i) := by
  apply DirectSum.linearMap_ext ℤ
  intro j
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, dsMap_lof]
  rw [DirectSum.component.of, DirectSum.component.of]
  split_ifs with h
  · subst h
    rfl
  · rw [map_zero]

/-- **A finite direct sum of exact pairs of linear maps is exact.** -/
theorem functionExact_dsMap {ι : Type*} [Fintype ι] [DecidableEq ι] {M N P : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module ℤ (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module ℤ (N i)]
    [∀ i, AddCommMonoid (P i)] [∀ i, Module ℤ (P i)]
    {f : ∀ i, M i →ₗ[ℤ] N i} {g : ∀ i, N i →ₗ[ℤ] P i}
    (h : ∀ i, Function.Exact ⇑(f i) ⇑(g i)) :
    Function.Exact ⇑(dsMap f) ⇑(dsMap g) := by
  intro y
  constructor
  · intro hy
    have hcomp : ∀ i, g i (y i) = 0 := by
      intro i
      have h1 : (DirectSum.component ℤ ι P i) (dsMap g y) = 0 := by rw [hy, map_zero]
      have h2 : (DirectSum.component ℤ ι P i) (dsMap g y) = g i (y i) := by
        rw [← LinearMap.comp_apply, component_dsMap g i, LinearMap.comp_apply]
        rfl
      rw [h2] at h1
      exact h1
    choose x hx using fun i => (h i (y i)).mp (hcomp i)
    refine ⟨∑ i, DirectSum.lof ℤ ι M i (x i), ?_⟩
    rw [map_sum]
    have h3 : ∀ i, dsMap f (DirectSum.lof ℤ ι M i (x i)) = DirectSum.lof ℤ ι N i (y i) := by
      intro i
      rw [dsMap_lof, hx i]
    rw [Finset.sum_congr rfl (fun i _ => h3 i), sum_lof_component y]
  · rintro ⟨x, hx⟩
    rw [← hx]
    have hx' : dsMap f x = ∑ i, DirectSum.lof ℤ ι N i (f i (x i)) := by
      conv_lhs => rw [← sum_lof_component x]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => dsMap_lof f i (x i))
    rw [hx', map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [dsMap_lof, (h i (f i (x i))).mpr ⟨x i, rfl⟩, map_zero]

/-! ## 2. Degreewise exactness of `A --f--> B --cokernel.π f--> cokernel f` -/

/-- **A short complex whose third map is the cokernel projection is exact.** -/
theorem shortComplex_cokernel_exact {A B : ChainComplex (ModuleCat ℤ) ℕ} (f : A ⟶ B) :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

/-- **Exactness in degree `n` of a short complex of chain complexes is exactness of its `n`-th
components.**  This is the degree-`n` case of the degreewise criterion
`Work.Serre.eval_exact_iff_function_exact` (`Submission/Work/Serre/relEZ_degreewise.lean`),
reproduced here under a distinct name so that this file depends only on `Mathlib` and the
`Kunneth` chapter. -/
theorem relEZ_eval_exact_iff_function_exact (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ))
    (n : ℕ) :
    (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).Exact ↔
      Function.Exact ((S.f).f n).hom ((S.g).f n).hom := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

/-- **Degreewise exactness of the cokernel projection.**  Since the evaluation functor
`HomologicalComplex.eval` is exact, exactness of the short complex of chain complexes
`A → B → cokernel f` descends to exactness of the pair of `ℤ`-linear maps
`(f.f q, (cokernel.π f).f q)`. -/
theorem functionExact_cokernelπ {A B : ChainComplex (ModuleCat ℤ) ℕ} (f : A ⟶ B) (q : ℕ) :
    Function.Exact ⇑((f.f q).hom) ⇑(((cokernel.π f).f q).hom) := by
  have h := ShortComplex.Exact.map (shortComplex_cokernel_exact f)
    (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) q)
  rwa [relEZ_eval_exact_iff_function_exact] at h

/-! ## 3. Tensoring with a flat component -/

/-- **Flatness: the degreewise exact pair survives tensoring with a flat component.** -/
theorem relEZ_exact_lTensor_cokernel (C A B : ChainComplex (ModuleCat ℤ) ℕ)
    (hC : ∀ n, Module.Flat ℤ ↥(C.X n)) (f : A ⟶ B) (p q : ℕ) :
    Function.Exact (LinearMap.lTensor ↥(C.X p) (f.f q).hom)
      (LinearMap.lTensor ↥(C.X p) ((cokernel.π f).f q).hom) := by
  haveI : Module.Flat ℤ ↥(C.X p) := hC p
  exact Module.Flat.lTensor_exact (R := ℤ) (M := ↥(C.X p)) (functionExact_cokernelπ f q)

/-- The same statement in the `TensorProduct.map id` form in which `tpMapLin` is written. -/
theorem exact_tensor_cokernel (C A B : ChainComplex (ModuleCat ℤ) ℕ)
    (hC : ∀ n, Module.Flat ℤ ↥(C.X n)) (f : A ⟶ B) (p q : ℕ) :
    Function.Exact
      (TensorProduct.map (LinearMap.id : ↥(C.X p) →ₗ[ℤ] ↥(C.X p)) ((f.f q).hom))
      (TensorProduct.map (LinearMap.id : ↥(C.X p) →ₗ[ℤ] ↥(C.X p))
        (((cokernel.π f).f q).hom)) := by
  simpa only [LinearMap.lTensor_def] using relEZ_exact_lTensor_cokernel C A B hC f p q

/-! ## 4. `tpMapLin` as a direct sum of its bidegree blocks -/

/-- **`tpMapLin` is the direct sum of its bidegree blocks** `id ⊗ g_q`, indexed by `tpIdx n`. -/
theorem tpMapLin_eq_dsMap (C D D' : ChainComplex (ModuleCat ℤ) ℕ) (g : D ⟶ D') (n : ℕ) :
    tpMapLin C C D D' (𝟙 C) g n
      = dsMap (fun pq : tpIdx n =>
          TensorProduct.map (LinearMap.id : ↥(C.X pq.1.1) →ₗ[ℤ] ↥(C.X pq.1.1))
            ((g.f pq.1.2).hom)) := by
  apply DirectSum.linearMap_ext ℤ
  intro pq
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply, LinearMap.comp_apply, tpMapLin_tpLof]
  simp only [HomologicalComplex.id_f, ModuleCat.hom_id]
  exact (dsMap_lof (M := fun pq : tpIdx n => tpSummand C D pq.1.1 pq.1.2)
    (N := fun pq : tpIdx n => tpSummand C D' pq.1.1 pq.1.2)
    (fun pq : tpIdx n =>
      TensorProduct.map (LinearMap.id : ↥(C.X pq.1.1) →ₗ[ℤ] ↥(C.X pq.1.1))
        ((g.f pq.1.2).hom)) pq z).symm

/-! ## 5. The main theorem -/

/-- **Exactness of the tensor product of a chain map with a degreewise flat complex.** -/
theorem relEZ_tpMapLin_exact (C : ChainComplex (ModuleCat ℤ) ℕ) (hC : ∀ n, Module.Flat ℤ ↥(C.X n))
    {A B : ChainComplex (ModuleCat ℤ) ℕ} (f : A ⟶ B) (n : ℕ) :
    Function.Exact (Work.Kunneth.tpMapLin C C A B (CategoryTheory.CategoryStruct.id C) f n)
      (Work.Kunneth.tpMapLin C C B (CategoryTheory.Limits.cokernel f)
        (CategoryTheory.CategoryStruct.id C) (CategoryTheory.Limits.cokernel.π f) n) := by
  rw [tpMapLin_eq_dsMap C A B f n,
    tpMapLin_eq_dsMap C B (CategoryTheory.Limits.cokernel f)
      (CategoryTheory.Limits.cokernel.π f) n]
  exact functionExact_dsMap (fun pq => exact_tensor_cokernel C A B hC f pq.1.1 pq.1.2)

end

end Work.Serre
