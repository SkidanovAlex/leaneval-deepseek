/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The cup-1 product (Steenrod's first cup product) on simplicial cochains

For cochains `u : C^P(S;R)` and `v : C^Q(S;R)` the *cup-1* cochain
`u ⌣₁ v : C^{P+Q-1}(S;R)` is defined by

`(u ⌣₁ v)(τ) = Σ_{f=0}^{P-1} (-1)^{f + (P-1-f)Q} · u(τ|_{A_f}) · v(τ|_{B_f})`

where, for a `(P+Q-1)`-simplex `τ` and `0 ≤ f < P`,

* `B_f` is the "middle" interval `[f, f+Q]` of vertices (a `Q`-simplex), and
* `A_f` is the complementary two-block set `[0,f] ∪ [f+Q, P+Q-1]` (a `P`-simplex).

Geometrically, the pairs `(A_f, B_f)` run through the "two-block joins" that cut the
`(P+Q-1)`-simplex at the two vertices `f` and `f+Q`; the alternating signs are the signs of
Steenrod's cup-1 product.  This cochain satisfies the *graded Leibniz rule*

`δ(u ⌣₁ v) + (δu) ⌣₁ v + (-1)^P u ⌣₁ (δv) = (-1)^{PQ}(v ⌣ u) - (u ⌣ v)`

(the "cup-1 relation", proved in `Submission/Work/Cohomology/cupOne_relation.lean`), which is
exactly the statement that the cup product on cohomology is graded commutative.

## Main definitions

* `Submission.Cohomology.joinFace`, `Submission.Cohomology.splitFace`: the two block inclusions.
* `Submission.Cohomology.cupOneOf`: the cup-1 product, with the ambient degree `n` and the
  equation `h : P + Q = n + 1` explicit (so that no `Nat`-arithmetic casts appear).
-/
import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

variable {S : SSet.{0}} {R : Type} [CommRing R]

/-- The monotone map `⦋P⦌ ⟶ ⦋n⦌` (where `P + Q = n + 1`) with image the two-block set
`{0,…,f} ∪ {f+Q,…,n}`, i.e. the identity on `0,1,…,f` followed by the shift by `Q-1`.
This is the "join" `[0,f] ∗ [f+Q,n]` of the two end blocks. -/
def joinFace {P Q n : ℕ} (h : P + Q = n + 1) (f : Fin P) : ⦋P⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    { toFun := fun k => ⟨if (k : ℕ) ≤ (f : ℕ) then (k : ℕ) else (k : ℕ) + Q - 1, by
        split_ifs with hk
        · omega
        · omega⟩
      monotone' := by
        intro a b hab
        simp only [Fin.mk_le_mk]
        split_ifs with ha hb hb
        · omega
        · omega
        · omega
        · omega }

/-- The monotone map `⦋Q⦌ ⟶ ⦋n⦌` (where `P + Q = n + 1`) with image the interval
`{f, f+1, …, f+Q}`, i.e. `k ↦ f + k`.  This is the "middle" block. -/
def splitFace {P Q n : ℕ} (h : P + Q = n + 1) (f : Fin P) : ⦋Q⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom
    { toFun := fun k => ⟨(f : ℕ) + (k : ℕ), by omega⟩
      monotone' := by
        intro a b hab
        simp only [Fin.mk_le_mk]
        omega }

@[simp]
lemma joinFace_apply {P Q n : ℕ} (h : P + Q = n + 1) (f : Fin P) (k : Fin (P + 1)) :
    ((joinFace h f).toOrderHom k : ℕ) =
      if (k : ℕ) ≤ (f : ℕ) then (k : ℕ) else (k : ℕ) + Q - 1 := rfl

@[simp]
lemma splitFace_apply {P Q n : ℕ} (h : P + Q = n + 1) (f : Fin P) (k : Fin (Q + 1)) :
    ((splitFace h f).toOrderHom k : ℕ) = (f : ℕ) + (k : ℕ) := rfl

/-- **The cup-1 product of cochains.**  For `u : C^P(S;R)`, `v : C^Q(S;R)` this is the
`(P+Q-1)`-cochain given on a simplex `τ` by
`Σ_{f<P} (-1)^{f + (P-1-f)Q} · u(τ|_{{0..f} ∪ {f+Q..P+Q-1}}) · v(τ|_{{f..f+Q}})`.

The ambient degree `n` and the equation `h : P + Q = n + 1` are explicit so that the
cup-1 relation can be stated without `Nat`-arithmetic casts. -/
def cupOneOf (S : SSet.{0}) (R : Type) [CommRing R] {P Q n : ℕ} (h : P + Q = n + 1)
    (u : Cochain S R P) (v : Cochain S R Q) : Cochain S R n :=
  fun τ => ∑ f : Fin P, (-1 : ℤ) ^ ((f : ℕ) + (P - 1 - (f : ℕ)) * Q) •
    (u (S.map (joinFace h f).op τ) * v (S.map (splitFace h f).op τ))

@[simp]
lemma cupOneOf_apply {P Q n : ℕ} (h : P + Q = n + 1) (u : Cochain S R P)
    (v : Cochain S R Q) (τ : S.obj (op ⦋n⦌)) :
    cupOneOf S R h u v τ = ∑ f : Fin P, (-1 : ℤ) ^ ((f : ℕ) + (P - 1 - (f : ℕ)) * Q) •
      (u (S.map (joinFace h f).op τ) * v (S.map (splitFace h f).op τ)) := rfl

@[simp]
lemma cupOneOf_zero_left {P Q n : ℕ} (h : P + Q = n + 1) (v : Cochain S R Q) :
    cupOneOf S R h (0 : Cochain S R P) v = 0 := by
  ext τ
  simp [cupOneOf_apply]

@[simp]
lemma cupOneOf_zero_right {P Q n : ℕ} (h : P + Q = n + 1) (u : Cochain S R P) :
    cupOneOf S R h u (0 : Cochain S R Q) = 0 := by
  ext τ
  simp [cupOneOf_apply]

lemma cupOneOf_add_left {P Q n : ℕ} (h : P + Q = n + 1) (u₁ u₂ : Cochain S R P)
    (v : Cochain S R Q) :
    cupOneOf S R h (u₁ + u₂) v = cupOneOf S R h u₁ v + cupOneOf S R h u₂ v := by
  ext τ
  simp only [cupOneOf_apply, Pi.add_apply, add_mul, smul_add, Finset.sum_add_distrib]

lemma cupOneOf_add_right {P Q n : ℕ} (h : P + Q = n + 1) (u : Cochain S R P)
    (v₁ v₂ : Cochain S R Q) :
    cupOneOf S R h u (v₁ + v₂) = cupOneOf S R h u v₁ + cupOneOf S R h u v₂ := by
  ext τ
  simp only [cupOneOf_apply, Pi.add_apply, mul_add, smul_add, Finset.sum_add_distrib]

lemma cupOneOf_smul_right {P Q n : ℕ} (h : P + Q = n + 1) (r : R) (u : Cochain S R P)
    (v : Cochain S R Q) :
    cupOneOf S R h u (r • v) = r • cupOneOf S R h u v := by
  ext τ
  simp only [cupOneOf_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

end

end Submission.Cohomology
