/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The cup product on simplicial cochains

For a simplicial set `S`, the cup product of cochains `u : C^p` and `v : C^q` is the cochain
`u ⌣ v : C^{p+q}` given on a `(p+q)`-simplex `σ` by

`(u ⌣ v)(σ) = u (σ|_{0…p}) · v (σ|_{p…p+q})`

(front `p`-face times back `q`-face, the two faces meeting in the vertex `p`: this is the dual of
the Alexander–Whitney map).

Because the cochain type `C^n := (S _⦋n⦌ → R)` is indexed by `ℕ` and Lean's `Nat.add` is not
definitionally associative, we define the primitive operation `cupOf` with the *ambient* degree `n`
and an explicit equation `h : p + q = n`; the Leibniz rule

`δ (u ⌣ v) = δu ⌣ v + (-1)^p u ⌣ δv`

can then be stated without any cast (both sides live in `C^{n+1}`).  The ordinary cup product is
`cup u v := cupOf rfl u v`.

The Leibniz rule is proved in `Submission/Work/Cohomology/cupOf_coboundary.lean`.
-/
import Mathlib
import Submission.Work.Cohomology.Basic

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

/-- The front face inclusion `⦋p⦌ ⟶ ⦋p+q⦌` (vertices `0,…,p`). -/
def frontFace (p q : ℕ) : ⦋p⦌ ⟶ ⦋p + q⦌ := SimplexCategory.subinterval 0 p (by omega)

/-- The back face inclusion `⦋q⦌ ⟶ ⦋p+q⦌` (vertices `p,…,p+q`). -/
def backFace (p q : ℕ) : ⦋q⦌ ⟶ ⦋p + q⦌ := SimplexCategory.subinterval p q (by omega)

/-- The front `p`-face of a simplex of degree `n`, where `h : p + q = n`. -/
def frontOf (S : SSet.{0}) {n p q : ℕ} (h : p + q = n) :
    S.obj (op ⦋n⦌) → S.obj (op ⦋p⦌) :=
  S.map (SimplexCategory.subinterval 0 p (by omega)).op

/-- The back `q`-face of a simplex of degree `n`, where `h : p + q = n`. -/
def backOf (S : SSet.{0}) {n p q : ℕ} (h : p + q = n) :
    S.obj (op ⦋n⦌) → S.obj (op ⦋q⦌) :=
  S.map (SimplexCategory.subinterval p q (by omega)).op

/-- The cup product, with the ambient degree `n` and the splitting `h : p + q = n` explicit. -/
def cupOf (S : SSet.{0}) (R : Type) [CommRing R] {n p q : ℕ} (h : p + q = n)
    (u : Cochain S R p) (v : Cochain S R q) : Cochain S R n :=
  fun σ => u (frontOf S h σ) * v (backOf S h σ)

/-- The cup product of a `p`-cochain and a `q`-cochain. -/
def cup (S : SSet.{0}) (R : Type) [CommRing R] {p q : ℕ}
    (u : Cochain S R p) (v : Cochain S R q) : Cochain S R (p + q) :=
  cupOf S R rfl u v

/-- The unit `0`-cochain. -/
def oneCochain (S : SSet.{0}) (R : Type) [CommRing R] : Cochain S R 0 := fun _ => 1

@[simp] lemma cupOf_apply (S : SSet.{0}) (R : Type) [CommRing R] {n p q : ℕ}
    (h : p + q = n) (u : Cochain S R p) (v : Cochain S R q) (σ : S.obj (op ⦋n⦌)) :
    cupOf S R h u v σ = u (frontOf S h σ) * v (backOf S h σ) := rfl

@[simp] lemma cup_apply (S : SSet.{0}) (R : Type) [CommRing R] {p q : ℕ}
    (u : Cochain S R p) (v : Cochain S R q) (σ : S.obj (op ⦋p + q⦌)) :
    cup S R u v σ = u (frontOf S rfl σ) * v (backOf S rfl σ) := rfl

lemma cupOf_add_left (S : SSet.{0}) (R : Type) [CommRing R] {n p q : ℕ}
    (h : p + q = n) (u₁ u₂ : Cochain S R p) (v : Cochain S R q) :
    cupOf S R h (u₁ + u₂) v = cupOf S R h u₁ v + cupOf S R h u₂ v := by
  ext σ; simp [add_mul]

lemma cupOf_add_right (S : SSet.{0}) (R : Type) [CommRing R] {n p q : ℕ}
    (h : p + q = n) (u : Cochain S R p) (v₁ v₂ : Cochain S R q) :
    cupOf S R h u (v₁ + v₂) = cupOf S R h u v₁ + cupOf S R h u v₂ := by
  ext σ; simp [mul_add]

lemma cupOf_smul_left (S : SSet.{0}) (R : Type) [CommRing R] {n p q : ℕ}
    (h : p + q = n) (r : R) (u : Cochain S R p) (v : Cochain S R q) :
    cupOf S R h (r • u) v = r • cupOf S R h u v := by
  ext σ; simp [mul_assoc]

lemma cupOf_smul_right (S : SSet.{0}) (R : Type) [CommRing R] {n p q : ℕ}
    (h : p + q = n) (r : R) (u : Cochain S R p) (v : Cochain S R q) :
    cupOf S R h u (r • v) = r • cupOf S R h u v := by
  ext σ; simp [mul_comm, mul_assoc]

@[simp] lemma cupOf_zero_left (S : SSet.{0}) (R : Type) [CommRing R] {n p q : ℕ}
    (h : p + q = n) (v : Cochain S R q) : cupOf S R h 0 v = 0 := by
  ext σ; simp [cupOf_apply]

@[simp] lemma cupOf_zero_right (S : SSet.{0}) (R : Type) [CommRing R] {n p q : ℕ}
    (h : p + q = n) (u : Cochain S R p) : cupOf S R h u 0 = 0 := by
  ext σ; simp [cupOf_apply]

/-- `(-1)^p • ((-1)^p • x) = x` in an additive commutative group. -/
lemma negOnePow_smul_smul {M : Type*} [AddCommGroup M] (p : ℕ) (x : M) :
    (-1 : ℤ) ^ p • ((-1 : ℤ) ^ p • x) = x := by
  rw [smul_smul, ← pow_add, show p + p = 2 * p from by ring, pow_mul]
  norm_num

/-- Pullback of cochains along a morphism of simplicial sets. -/
def pullbackCo {S T : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) {n : ℕ}
    (u : Cochain T R n) : Cochain S R n :=
  u ∘ f.app (op ⦋n⦌)

@[simp] lemma pullbackCo_apply {S T : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) {n : ℕ}
    (u : Cochain T R n) (σ : S.obj (op ⦋n⦌)) :
    pullbackCo R f u σ = u (f.app (op ⦋n⦌) σ) := rfl

/-- Naturality of the front face. -/
lemma frontOf_natural {S T : SSet.{0}} (f : S ⟶ T) {n p q : ℕ} (h : p + q = n)
    (σ : S.obj (op ⦋n⦌)) :
    f.app (op ⦋p⦌) (frontOf S h σ) = frontOf T h (f.app (op ⦋n⦌) σ) :=
  ConcreteCategory.congr_hom (f.naturality (SimplexCategory.subinterval 0 p (by omega)).op) σ

/-- Naturality of the back face. -/
lemma backOf_natural {S T : SSet.{0}} (f : S ⟶ T) {n p q : ℕ} (h : p + q = n)
    (σ : S.obj (op ⦋n⦌)) :
    f.app (op ⦋q⦌) (backOf S h σ) = backOf T h (f.app (op ⦋n⦌) σ) :=
  ConcreteCategory.congr_hom (f.naturality (SimplexCategory.subinterval p q (by omega)).op) σ

lemma pullbackCo_coboundary {S T : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) (n : ℕ)
    (u : Cochain T R n) :
    pullbackCo R f (coboundary T R n u) = coboundary S R n (pullbackCo R f u) := by
  ext σ
  simp only [coboundary_apply, pullbackCo_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← SSet.δ_naturality_apply f i σ]

lemma pullbackCo_cupOf {S T : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) {n p q : ℕ}
    (h : p + q = n) (u : Cochain T R p) (v : Cochain T R q) :
    pullbackCo R f (cupOf T R h u v) = cupOf S R h (pullbackCo R f u) (pullbackCo R f v) := by
  ext σ
  simp only [cupOf_apply, pullbackCo_apply, frontOf_natural f h σ, backOf_natural f h σ]

end

end Submission.Cohomology
