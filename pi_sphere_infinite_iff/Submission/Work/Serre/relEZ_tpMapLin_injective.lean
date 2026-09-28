import Mathlib
import Submission.Work.Kunneth.Chapter

/-!
# Injectivity of the relative Eilenberg–Zilber comparison `C ⊗ (A ⟶ B)`

For a chain complex `C` of `ℤ`-modules that is **degreewise flat**, tensoring with `C` is exact, so
the relative Eilenberg–Zilber comparison map

`Work.Kunneth.tpMapLin C C A B (𝟙 C) f n : (C ⊗ A)_n ⟶ (C ⊗ B)_n`

of a chain map `f : A ⟶ B` with degreewise injective components is injective (in every degree).
This is the "left exactness" half of the exactness of the functor `D ↦ tpC C D`, used in the Serre
chapter to identify the relative homology `H_*(W × (P,Q))` with `H_*(C_*(W) ⊗ C_*(P,Q))`.

The proof is a two-step reduction, both steps completely elementary:

* `(C ⊗ A)_n = ⨁_{p+q=n} C_p ⊗ A_q`, and on the summand `(p,q)` the map is the tensor product
  `C_p ⊗ A_q → C_p ⊗ B_q` of `1` with `f_q`, i.e. `LinearMap.lTensor C_p f_q`. Since `C_p` is flat
  and `f_q` is injective, this summand map is injective
  (`Module.Flat.lTensor_preserves_injective_linearMap`);
* a map `⨁_i M_i → ⨁_i N_i` given by the universal property out of the componentwise maps is
  injective as soon as every component is (`directSum_lof_comp_injective`, proved below).
-/

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

-- The chapter `Work.Kunneth` is written with the generic `ℤ`-module structure
-- `AddCommGroup.toIntModule` disabled and the `ModuleCat` structure `ModuleCat.isModule`
-- in effect; the statement below is unchanged by this (the two structures are propositionally
-- equal and `isDefEq` at the type of the statement), but the *proof* needs the same convention.
attribute [-instance] AddCommGroup.toIntModule

namespace Work.Serre

noncomputable section

/-! ## Direct sums of injective maps -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M N : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module ℤ (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module ℤ (N i)]

/-- The componentwise map `(∀ i, M i) →ₗ (∀ i, N i)` induced by a family of linear maps. -/
def funMap (ψ : ∀ i, M i →ₗ[ℤ] N i) : (∀ i, M i) →ₗ[ℤ] (∀ i, N i) where
  toFun w i := ψ i (w i)
  map_add' a b := by funext i; simp
  map_smul' c a := by funext i; simp

lemma funMap_apply (ψ : ∀ i, M i →ₗ[ℤ] N i) (w : ∀ i, M i) (i : ι) :
    funMap ψ w i = ψ i (w i) := rfl

/-- **A coproduct of injective maps is injective.**  If every `ψ i` is injective, then so is the
linear map `⨁ i, M i → ⨁ i, N i` whose `i`-th component is `lof i ∘ ψ i`.  (Injectivity of a
coproduct of maps is where the finiteness of the index set enters, via
`DirectSum.linearEquivFunOnFintype`.) -/
theorem directSum_lof_comp_injective (ψ : ∀ i, M i →ₗ[ℤ] N i)
    (hψ : ∀ i, Function.Injective (ψ i)) :
    Function.Injective (DirectSum.toModule ℤ ι (DirectSum ι N)
      (fun i => (DirectSum.lof ℤ ι N i).comp (ψ i))) := by
  intro x y hxy
  -- Identify the map with the componentwise map on `∀ i, M i` under the linear equivalence
  -- `DirectSum.linearEquivFunOnFintype`.
  have key : ∀ x : DirectSum ι M, (DirectSum.linearEquivFunOnFintype ℤ ι N)
      ((DirectSum.toModule ℤ ι (DirectSum ι N) (fun i => (DirectSum.lof ℤ ι N i).comp (ψ i))) x)
      = funMap ψ ((DirectSum.linearEquivFunOnFintype ℤ ι M) x) := by
    have h : (DirectSum.linearEquivFunOnFintype ℤ ι N).toLinearMap ∘ₗ
          (DirectSum.toModule ℤ ι (DirectSum ι N) (fun i => (DirectSum.lof ℤ ι N i).comp (ψ i)))
        = (funMap ψ) ∘ₗ (DirectSum.linearEquivFunOnFintype ℤ ι M).toLinearMap := by
      apply DirectSum.linearMap_ext ℤ
      intro i
      apply LinearMap.ext
      intro m
      funext j
      simp only [LinearMap.comp_apply, DirectSum.toModule_lof, LinearEquiv.coe_coe,
        DirectSum.linearEquivFunOnFintype_lof, funMap_apply]
      by_cases hji : j = i
      · subst hji; simp
      · simp [Pi.single_eq_of_ne hji]
    intro x
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using LinearMap.congr_fun h x
  have h1 := key x
  have h2 := key y
  rw [hxy] at h1
  have h3 : funMap ψ ((DirectSum.linearEquivFunOnFintype ℤ ι M) x)
      = funMap ψ ((DirectSum.linearEquivFunOnFintype ℤ ι M) y) := by
    rw [← h1, ← h2]
  have h4 : (DirectSum.linearEquivFunOnFintype ℤ ι M) x
      = (DirectSum.linearEquivFunOnFintype ℤ ι M) y := by
    funext i
    exact hψ i (congrFun h3 i)
  exact (DirectSum.linearEquivFunOnFintype ℤ ι M).injective h4

/-! ## The tensor product with a degreewise flat complex preserves injectivity -/

open Work.Kunneth

theorem relEZ_tpMapLin_injective (C : ChainComplex (ModuleCat ℤ) ℕ) (hC : ∀ n, Module.Flat ℤ ↥(C.X n))
    {A B : ChainComplex (ModuleCat ℤ) ℕ} (f : A ⟶ B) (hf : ∀ n, Function.Injective (f.f n).hom)
    (n : ℕ) : Function.Injective
      (Work.Kunneth.tpMapLin C C A B (CategoryTheory.CategoryStruct.id C) f n) := by
  -- On the `(p,q)`-summand the comparison map is `lTensor C_p f_q`, which is injective by flatness.
  have hψ : ∀ pq : tpIdx n, Function.Injective
      (TensorProduct.map (LinearMap.id : ↥(C.X pq.1.1) →ₗ[ℤ] ↥(C.X pq.1.1))
        ((f.f pq.1.2).hom)) := by
    intro pq
    rw [← LinearMap.lTensor_def]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (hf pq.1.2)
  have hmain := directSum_lof_comp_injective
    (M := fun pq : tpIdx n => tpSummand C A pq.1.1 pq.1.2)
    (N := fun pq : tpIdx n => tpSummand C B pq.1.1 pq.1.2)
    (fun pq => TensorProduct.map (LinearMap.id : ↥(C.X pq.1.1) →ₗ[ℤ] ↥(C.X pq.1.1))
      ((f.f pq.1.2).hom)) hψ
  convert hmain using 2
  ext x pq
  simp only [tpMapLin, HomologicalComplex.id_f, ModuleCat.hom_id, tpLof, tpX]

end

end Work.Serre
