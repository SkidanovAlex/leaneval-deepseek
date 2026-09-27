/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The Eilenberg–Zilber shuffle chain of a pair of simplices

For a simplicial set `S` and a commutative ring `R`, `Submission.Cohomology.SChain S R n` is the
`R`-module of finitely supported functions on the `n`-simplices of `S`.  For `X`, `Y` the
monoidal (cartesian) structure on `SSet` has `(X ⊗ Y).obj (op ⦋n⦌) = X.obj (op ⦋n⦌) × Y.obj (op ⦋n⦌)`.

The **Eilenberg–Zilber (shuffle) chain** of a pair of simplices `a ∈ X_p`, `b ∈ Y_q` is the
`(p+q)`-chain of `X ⊗ Y`

`EZ(a ⊗ b) = Σ_{A ⊆ {0,…,p+q-1}, |A| = p} ε(A) • single ((a ∘ h_A) , (b ∘ g_A))`

where, for such a `(p,q)`-shuffle `A`,

* `h_A : ⦋p+q⦌ ⟶ ⦋p⦌` is the monotone map `j ↦ #{i ∈ A : i < j}`,
* `g_A : ⦋p+q⦌ ⟶ ⦋q⦌` is the monotone map `j ↦ #{i ∉ A : i < j}`,
* `ε(A) = (-1)^{#{(i,j) : i ∈ A, j ∉ A, j < i}}` is the sign of the shuffle permutation.

The two properties of this chain that are used downstream are

* `ezChainB_sbdry` (the "shuffle lemma"): the boundary of the shuffle chain is the sum of the
  shuffle chains of the faces with the Koszul signs,
* `ezChainB_cup` (the pairing with the cup product of two *normalized* cocycles): it evaluates
  to `u a * v b`.  The proof of the latter is elementary: for every shuffle `A ≠ {0,…,p-1}`
  the map `h_A ∣ {0,…,p}` (i.e. the front `p`-face of `a ∘ h_A`) is *not* injective, hence
  `(a ∘ h_A)` has a repeated vertex, so a normalized cochain `u` evaluates to `0` on it.
-/
import Mathlib
import Submission.Work.Cohomology.Chains

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

noncomputable section

/-- The number of elements of `A` that are strictly below `j`. -/
def aCnt {p q : ℕ} (A : Finset (Fin (p + q))) (j : Fin (p + q + 1)) : ℕ :=
  (A.filter fun i : Fin (p + q) => i.val < j.val).card

/-- The number of elements outside `A` that are strictly below `j`. -/
def bCnt {p q : ℕ} (A : Finset (Fin (p + q))) (j : Fin (p + q + 1)) : ℕ :=
  ((Finset.univ \ A).filter fun i : Fin (p + q) => i.val < j.val).card

lemma aCnt_le {p q : ℕ} (A : Finset (Fin (p + q))) (hA : A.card = p)
    (j : Fin (p + q + 1)) : aCnt A j ≤ p := by
  have h : aCnt A j ≤ A.card := Finset.card_le_card (Finset.filter_subset _ _)
  omega

lemma bCnt_le {p q : ℕ} (A : Finset (Fin (p + q))) (hA : A.card = p)
    (j : Fin (p + q + 1)) : bCnt A j ≤ q := by
  have h₁ : bCnt A j ≤ (Finset.univ \ A).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h₂ : (Finset.univ \ A : Finset (Fin (p + q))).card = p + q - A.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, Fintype.card_fin]
  omega

lemma aCnt_mono {p q : ℕ} (A : Finset (Fin (p + q))) : Monotone (aCnt A) := by
  intro i j hij
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, lt_of_lt_of_le hk.2 hij⟩

lemma bCnt_mono {p q : ℕ} (A : Finset (Fin (p + q))) : Monotone (bCnt A) := by
  intro i j hij
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, lt_of_lt_of_le hk.2 hij⟩

/-- The "a-side" of a `(p,q)`-shuffle: the monotone map `j ↦ #{i ∈ A : i < j}`. -/
def shuffleMapA {p q : ℕ} (A : Finset (Fin (p + q))) (hA : A.card = p) : ⦋p + q⦌ ⟶ ⦋p⦌ :=
  SimplexCategory.mkHom
    { toFun := fun j => ⟨aCnt A j, by have := aCnt_le A hA j; omega⟩
      monotone' := aCnt_mono A }

/-- The "b-side" of a `(p,q)`-shuffle: the monotone map `j ↦ #{i ∉ A : i < j}`. -/
def shuffleMapB {p q : ℕ} (A : Finset (Fin (p + q))) (hA : A.card = p) : ⦋p + q⦌ ⟶ ⦋q⦌ :=
  SimplexCategory.mkHom
    { toFun := fun j => ⟨bCnt A j, by have := bCnt_le A hA j; omega⟩
      monotone' := bCnt_mono A }

/-- The sign of a `(p,q)`-shuffle: `(-1)` to the number of inversions `#{(i,j) : i ∈ A, j ∉ A,
j < i}`. -/
def shuffleSign {p q : ℕ} (A : Finset (Fin (p + q))) : ℤ :=
  (-1 : ℤ) ^ (A.sum fun i => ((Finset.univ \ A).filter fun j : Fin (p + q) => j.val < i.val).card)

/-- The staircase simplex of a `(p,q)`-shuffle, applied to `a ∈ X_p` and `b ∈ Y_q`: an element of
`(X ⊗ Y)_{p+q}`. -/
def staircase {X Y : SSet.{0}} {p q : ℕ} (A : Finset (Fin (p + q))) (hA : A.card = p)
    (a : X.obj (op ⦋p⦌)) (b : Y.obj (op ⦋q⦌)) :
    (MonoidalCategoryStruct.tensorObj X Y).obj (op ⦋p + q⦌) :=
  (X.map (shuffleMapA A hA).op a, Y.map (shuffleMapB A hA).op b)

/-- The Eilenberg–Zilber chain of a pair of simplices `a ∈ X_p`, `b ∈ Y_q`, as a chain of `X ⊗ Y`
in degree `p + q`. -/
def ezChainB {X Y : SSet.{0}} {p q : ℕ} (a : X.obj (op ⦋p⦌)) (b : Y.obj (op ⦋q⦌)) :
    Submission.Cohomology.SChain (MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q) :=
  ∑ A : {A : Finset (Fin (p + q)) // A.card = p},
    (shuffleSign A.1 : ℚ) • Finsupp.single (staircase A.1 A.2 a b) 1

/-- The shuffle `A = {0,1,…,p-1}` (all "a-steps" first). -/
def shuffleId (p q : ℕ) : Finset (Fin (p + q)) :=
  Finset.univ.filter fun i : Fin (p + q) => i.val < p

/-- A cochain is *normalized* if it vanishes on all degenerate simplices. -/
def IsNormalized {S : SSet.{0}} {n : ℕ} (u : Submission.Cohomology.Cochain S ℚ n) : Prop :=
  ∀ σ : S.obj (op ⦋n⦌), σ ∈ S.degenerate n → u σ = 0

end

end Work.Cohomology
