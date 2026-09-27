/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Chains of a simplicial set, dual to the cochains

For a simplicial set `S` and a commutative ring `R`, the `n`-chains of `S` are the
*finitely supported* functions on the `n`-simplices,

`SChain S R n := S _⦋n⦌ →₀ R`,

so that the cochain module `Cochain S R n = (S _⦋n⦌ → R)` is naturally the dual of
`SChain S R n` (evaluation of a function on a finitely supported chain).

The boundary `sbdry : SChain S R (n+1) →ₗ[R] SChain S R n` is the transpose of the coboundary
`coboundary S R n`, and the evaluation `seval` is the pairing

`seval u c = ∑ σ, c σ * u σ`.

The point of this file is to provide the chain-level language in which the chain homotopy
theory (subdivision, Eilenberg–Zilber, …) of our cohomology can be stated.
-/
import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.Cohomology

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

/-- The `R`-module of `n`-chains of a simplicial set: finitely supported functions on the
`n`-simplices. -/
abbrev SChain (S : SSet.{0}) (R : Type) [Zero R] (n : ℕ) := S.obj (op ⦋n⦌) →₀ R

/-- The evaluation pairing of a cochain on a chain. -/
def seval (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) (u : Cochain S R n) :
    SChain S R n →ₗ[R] R :=
  Finsupp.linearCombination R u

lemma seval_apply (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) (u : Cochain S R n)
    (c : SChain S R n) : seval S R n u c = c.sum fun σ m => m * u σ := by
  rw [seval, Finsupp.linearCombination_apply]
  simp

lemma seval_single (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) (u : Cochain S R n)
    (σ : S.obj (op ⦋n⦌)) (m : R) :
    seval S R n u (Finsupp.single σ m) = m * u σ := by
  rw [seval_apply, Finsupp.sum_single_index (by simp)]

/-- The boundary `∂ : C_{n+1} → C_n` of chains: the transpose of the coboundary.  On a simplex
`σ` it is `∑ᵢ (-1)ⁱ (δᵢ σ)`. -/
def sbdry (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) :
    SChain S R (n + 1) →ₗ[R] SChain S R n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.lmapDomain R R (S.δ i)

lemma sbdry_single (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ)
    (σ : S.obj (op ⦋n + 1⦌)) (m : R) :
    sbdry S R n (Finsupp.single σ m)
      = ∑ i : Fin (n + 2), Finsupp.single (S.δ i σ) (((-1 : ℤ) ^ (i : ℕ)) • m) := by
  classical
  simp only [sbdry, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Finsupp.smul_single]

private lemma seval_coboundary_single (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ)
    (u : Cochain S R n) (σ : S.obj (op ⦋n + 1⦌)) (m : R) :
    seval S R (n + 1) (coboundary S R n u) (Finsupp.single σ m)
      = seval S R n u (sbdry S R n (Finsupp.single σ m)) := by
  rw [seval_single, coboundary_apply, sbdry_single, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [seval_single, zsmul_eq_mul]
  push_cast
  ring

/-- The fundamental transpose identity: evaluating the coboundary on a chain is evaluating the
original cochain on the boundary. -/
theorem seval_coboundary (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ)
    (u : Cochain S R n) (c : SChain S R (n + 1)) :
    seval S R (n + 1) (coboundary S R n u) c = seval S R n u (sbdry S R n c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a b f ha hb ih =>
      simp only [map_add, ih, seval_coboundary_single]

/-- The `R`-submodule of `n`-cycles of the chain complex.  In degree `0` it is everything (there
is no boundary into degree `-1`). -/
def chainCycles (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) : Submodule R (SChain S R n) :=
  match n with
  | 0 => ⊤
  | m + 1 => LinearMap.ker (sbdry S R m)

lemma mem_chainCycles_succ {S : SSet.{0}} {R : Type} [CommRing R] {n : ℕ}
    {c : SChain S R (n+1)} : c ∈ chainCycles S R (n+1) ↔ sbdry S R n c = 0 := Iff.rfl

/-- The pushforward of chains along a morphism of simplicial sets. -/
def chainMap {S T : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) (n : ℕ) :
    SChain S R n →ₗ[R] SChain T R n :=
  Finsupp.lmapDomain R R (f.app (op ⦋n⦌))

@[simp] lemma chainMap_single {S T : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) (n : ℕ)
    (σ : S.obj (op ⦋n⦌)) (r : R) :
    chainMap R f n (Finsupp.single σ r) = Finsupp.single (f.app (op ⦋n⦌) σ) r := by
  rw [chainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The structure maps of a morphism of simplicial sets commute with the face maps. -/
lemma hom_app_δ {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ) (i : Fin (n+2))
    (σ : S.obj (op ⦋n+1⦌)) :
    f.app (op ⦋n⦌) (S.δ i σ) = T.δ i (f.app (op ⦋n+1⦌) σ) := by
  have h := f.naturality_apply (SimplexCategory.δ i).op σ
  simpa only [SimplicialObject.δ] using h

/-- The pushforward of chains along a morphism of simplicial sets is a chain map. -/
theorem chainMap_sbdry {S T : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) (n : ℕ)
    (c : SChain S R (n+1)) :
    chainMap R f n (sbdry S R n c) = sbdry T R n (chainMap R f (n+1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single σ r =>
      rw [chainMap_single, sbdry_single, sbdry_single, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [chainMap_single, hom_app_δ]

/-- The evaluation pairing is natural with respect to the pushforward of chains along a morphism
of simplicial sets. -/
lemma seval_chainMap {S T : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) (n : ℕ)
    (u : Cochain T R n) (c : SChain S R n) :
    seval T R n u (chainMap R f n c) = seval S R n (pullbackCo R f u) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single σ r => rw [chainMap_single, seval_single, seval_single]; rfl

/-- The `R`-submodule of `n`-boundaries of the chain complex of a simplicial set: the image of
`∂_{n+1} : C_{n+1} → C_n`. -/
def chainBoundaries (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) : Submodule R (SChain S R n) :=
  LinearMap.range (sbdry S R n)

lemma mem_chainBoundaries {S : SSet.{0}} {R : Type} [CommRing R] {n : ℕ}
    {c : SChain S R n} : c ∈ chainBoundaries S R n ↔ ∃ d, sbdry S R n d = c := Iff.rfl

/-- The boundaries, viewed as a submodule of the cycles. -/
def chainBoundariesInCycles (S : SSet.{0}) (R : Type) [CommRing R] (n : ℕ) :
    Submodule R (chainCycles S R n) :=
  (chainBoundaries S R n).comap (chainCycles S R n).subtype

/-- Cycles pair to zero with coboundaries: the pairing of a cohomology class with a cycle is
well defined. -/
theorem seval_coboundary_eq_zero {S : SSet.{0}} {R : Type} [CommRing R] {n : ℕ}
    (v : Cochain S R n) (c : SChain S R (n+1)) (hc : c ∈ chainCycles S R (n+1)) :
    seval S R (n+1) (coboundary S R n v) c = 0 := by
  rw [seval_coboundary, mem_chainCycles_succ.mp hc, map_zero]

end

end Submission.Cohomology
