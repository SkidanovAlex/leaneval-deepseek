/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Singular simplices on the subtype standard simplex (Lean v4.34 / Mathlib port bridge)

Mathlib now models the topological `n`-simplex by the structure `Convexity.StdSimplex ℝ (Fin (n+1))`,
and `TopCat.toSSetObjEquiv` identifies `n`-simplices of `Sing X` with `C(StdSimplex ℝ (Fin (n+1)), X)`.
This development works with the (now deprecated) subtype `stdSimplex ℝ (Fin (n+1))` of
`Fin (n+1) → ℝ`.  The two are homeomorphic (`stdSimplexHomeo`); `TopCat.toSSetObjEquivT` is
`TopCat.toSSetObjEquiv` transported along that homeomorphism, with the same naturality lemmas as the
old `TopCat.toSSetObjEquiv`.
-/
import Mathlib

set_option linter.deprecated false

open CategoryTheory Simplicial Opposite

noncomputable section

namespace Submission.Cohomology

/-- The subtype standard simplex is homeomorphic to Mathlib's `Convexity.StdSimplex`. -/
def stdSimplexHomeo (ι : Type) [Fintype ι] :
    stdSimplex ℝ ι ≃ₜ Convexity.StdSimplex ℝ ι where
  toFun x :=
    { weights := Finsupp.equivFunOnFinite.symm x.1
      nonneg := fun i => by simpa using x.2.1 i
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        simpa using x.2.2 }
  invFun w := ⟨w.weights, fun i => w.weights_nonneg i, w.total_of_fintype⟩
  left_inv x := by ext i; rfl
  right_inv w := by ext i; rfl
  continuous_toFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous_iff]
    exact continuous_subtype_val
  continuous_invFun :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous.subtype_mk _

@[simp] lemma stdSimplexHomeo_weights {ι : Type} [Fintype ι] (x : stdSimplex ℝ ι) (i : ι) :
    (stdSimplexHomeo ι x).weights i = (x : ι → ℝ) i := rfl

/-- The subtype simplex on a subsingleton index type is a subsingleton (Mathlib's instance for it
no longer applies to the subtype `stdSimplex ℝ ι`). -/
instance stdSimplex_subsingleton (ι : Type) [Fintype ι] [Subsingleton ι] :
    Subsingleton (stdSimplex ℝ ι) :=
  (stdSimplexHomeo ι).injective.subsingleton

lemma stdSimplexHomeo_map {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (f : ι → κ)
    (x : stdSimplex ℝ ι) :
    stdSimplexHomeo κ (stdSimplex.map f x)
      = Convexity.StdSimplex.map f (stdSimplexHomeo ι x) := by
  ext k
  rw [stdSimplexHomeo_weights, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    Convexity.StdSimplex.weights_map, Finsupp.mapDomain_fintype, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.single_apply, stdSimplexHomeo_weights]

end Submission.Cohomology

universe u

namespace TopCat

/-- `TopCat.toSSetObjEquiv`, with the subtype standard simplex `stdSimplex ℝ (Fin (n+1))` as the
source of the singular simplices. -/
def toSSetObjEquivT (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (toSSet.obj X).obj n ≃ C(stdSimplex ℝ (Fin (n.unop.len + 1)), X) :=
  (X.toSSetObjEquiv n).trans
    ((Submission.Cohomology.stdSimplexHomeo (Fin (n.unop.len + 1))).symm.continuousMapCongr
      (Homeomorph.refl X))

lemma toSSetObjEquivT_apply (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ) (x : (toSSet.obj X).obj n)
    (z : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    X.toSSetObjEquivT n x z
      = X.toSSetObjEquiv n x (Submission.Cohomology.stdSimplexHomeo _ z) := rfl

lemma toSSetObjEquivT_naturality_apply {X : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (x : (toSSet.obj X).obj (op m)) (z : stdSimplex ℝ (Fin (n.len + 1))) :
    X.toSSetObjEquivT (op n) ((toSSet.obj X).map f.op x) z
      = X.toSSetObjEquivT (op m) x (stdSimplex.map f z) := by
  rw [toSSetObjEquivT_apply, toSSetObjEquivT_apply, toSSetObjEquiv_naturality_apply,
    Submission.Cohomology.stdSimplexHomeo_map]

lemma toSSetObjEquivT_δ_apply {X : TopCat.{u}} {n : ℕ}
    (x : (toSSet.obj X).obj (op ⦋n + 1⦌)) (i : Fin (n + 2)) (z : stdSimplex ℝ (Fin (n + 1))) :
    X.toSSetObjEquivT (op ⦋n⦌) ((toSSet.obj X).δ i x) z
      = X.toSSetObjEquivT (op ⦋n + 1⦌) x (stdSimplex.map i.succAbove z) := by
  rw [toSSetObjEquivT_apply, toSSetObjEquivT_apply, toSSetObjEquiv_δ_apply,
    Submission.Cohomology.stdSimplexHomeo_map]

lemma toSSetObjEquivT_symm_naturality {X : TopCat.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (g : C(stdSimplex ℝ (Fin (m.len + 1)), X)) :
    (toSSet.obj X).map f.op ((X.toSSetObjEquivT _).symm g) =
      (X.toSSetObjEquivT _).symm (g.comp ⟨stdSimplex.map f, stdSimplex.continuous_map _⟩) := by
  apply (X.toSSetObjEquivT _).injective
  ext z
  rw [Equiv.apply_symm_apply, toSSetObjEquivT_naturality_apply, Equiv.apply_symm_apply]
  rfl

/-- Naturality of `toSSetObjEquivT` for a morphism of `SimplexCategoryᵒᵖ`. -/
lemma toSSetObjEquivT_map_apply' {X : TopCat.{u}} {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (toSSet.obj X).obj n) (z : stdSimplex ℝ (Fin (m.unop.len + 1))) :
    X.toSSetObjEquivT m ((toSSet.obj X).map f x) z
      = X.toSSetObjEquivT n x (stdSimplex.map f.unop z) :=
  toSSetObjEquivT_naturality_apply f.unop x z

/-- The point of a `0`-simplex, read through `toSSetObjEquivT` at any point of `Δ⁰`. -/
lemma toSSetObj₀Equiv_eq_T {X : TopCat.{u}} (x : (toSSet.obj X).obj (op ⦋0⦌))
    (z : stdSimplex ℝ (Fin (⦋0⦌.len + 1))) :
    toSSetObj₀Equiv x = X.toSSetObjEquivT (op ⦋0⦌) x z := by
  rw [toSSetObj₀Equiv_apply, toSSetObjEquivT_apply]
  congr 1
  haveI : Subsingleton (Fin (⦋0⦌.len + 1)) := ⟨fun a b => Fin.ext (by first | omega | simp | (simp; omega))⟩
  exact Subsingleton.elim _ _

lemma toSSetObjEquivT_σ_apply {X : TopCat.{u}} {n : ℕ}
    (x : (toSSet.obj X).obj (op ⦋n⦌)) (i : Fin (n + 1)) (z : stdSimplex ℝ (Fin (n + 2))) :
    X.toSSetObjEquivT (op ⦋n + 1⦌) ((toSSet.obj X).σ i x) z
      = X.toSSetObjEquivT (op ⦋n⦌) x (stdSimplex.map i.predAbove z) := by
  rw [toSSetObjEquivT_apply, toSSetObjEquivT_apply, toSSetObjEquiv_σ_apply,
    Submission.Cohomology.stdSimplexHomeo_map]

end TopCat
