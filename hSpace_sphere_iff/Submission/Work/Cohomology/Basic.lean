/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Cochains and the cochain complex of a simplicial set

Mathlib has singular *homology* (`AlgebraicTopology.SingularHomology`) but no cohomology.
This file starts the cohomology chapter: for a simplicial set `S` and a commutative ring `R` we
define the `R`-module of `n`-cochains

`Cochain S R n := (S _⦋n⦌ → R)`,

the coboundary `δ : C^n → C^{n+1}`, `(δf)(σ) = ∑ᵢ (-1)ⁱ f (S.δᵢ σ)`, and package it as an honest
`CochainComplex (ModuleCat R) ℕ` so that all of Mathlib's homological algebra (homology,
long exact sequences, tensor products, …) becomes available.  The cohomology of `S` is then
`cohomology S R n := (cochainComplex S R).homology n`.

The fact `δ² = 0` is the cosimplicial identity; it is proved separately (see
`Submission/Work/Cohomology/coboundary_comp.lean`).
-/
import Mathlib

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

/-- The `R`-module of `n`-cochains of a simplicial set `S`: all functions from the
`n`-simplices of `S` to `R`. -/
abbrev Cochain (S : SSet.{0}) (R : Type) (n : ℕ) := S.obj (op ⦋n⦌) → R

/-- Precomposition with a function `f : α → β`, as an `R`-linear map
`(β → R) →ₗ[R] (α → R)`. -/
def precomp (R : Type) [CommRing R] {α β : Type} (f : α → β) :
    (β → R) →ₗ[R] (α → R) where
  toFun g := g ∘ f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma precomp_apply {R : Type} [CommRing R] {α β : Type} (f : α → β) (g : β → R)
    (a : α) : precomp R f g a = g (f a) := rfl

/-- The coboundary: `(δ f)(σ) = ∑ᵢ (-1)ⁱ f (σ ∘ δᵢ)`. -/
def coboundary (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) :
    Cochain S R n →ₗ[R] Cochain S R (n + 1) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • precomp R (S.δ i)

lemma coboundary_apply (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) (f : Cochain S R n)
    (σ : S.obj (op ⦋n + 1⦌)) :
    coboundary S R n f σ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • f (S.δ i σ) := by
  simp only [coboundary, Finset.sum_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    precomp_apply, Pi.smul_apply]

end

end Submission.Cohomology
