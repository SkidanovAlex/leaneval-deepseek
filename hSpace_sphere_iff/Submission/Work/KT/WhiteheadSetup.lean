import Mathlib

/-!
# Helpers for Whitehead's lemma in block form (`Work.KT.whitehead_diag`)

Small, self-contained facts about `List.prod` / `List.sum` of pairwise-annihilating matrices,
about sums of `Matrix.single`-matrices across the two summands of `ι ⊕ ι`, and about
`Matrix.reindex` of a `single`-matrix.
-/

namespace Work.KT
namespace Whitehead

open Matrix

/-- If every `b` in `l` is right-annihilated by `A`, then so is `l.sum`. -/
lemma mul_list_sum_eq_zero {α : Type*} [Semiring α] {l : List α} {A : α}
    (h : ∀ b ∈ l, A * b = 0) : A * l.sum = 0 := by
  induction l with
  | nil => simp
  | cons b t ih =>
    rw [List.sum_cons, mul_add, h b (by simp), ih (fun b hb => h b (by simp [hb]))]
    simp

/-- Product of `1 + a` over a list whose elements pairwise multiply to zero. -/
lemma list_prod_one_add_of_pairwise_mul_eq_zero {α : Type*} [Semiring α] {l : List α}
    (h : ∀ a ∈ l, ∀ b ∈ l, a * b = 0) :
    (l.map (fun a => 1 + a)).prod = 1 + l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h' : ∀ x ∈ t, ∀ y ∈ t, x * y = 0 := fun x hx y hy => h x (by simp [hx]) y (by simp [hy])
    have ha : ∀ b ∈ t, a * b = 0 := fun b hb => h a (by simp) b (by simp [hb])
    have ha' : a * t.sum = 0 := mul_list_sum_eq_zero ha
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih h']
    rw [mul_add, mul_one, add_mul, one_mul, ha', add_zero, add_assoc]

/-- `Finset.sum` as a `List.sum` over `Finset.toList`. -/
lemma finset_sum_toList {M : Type*} [AddCommMonoid M] {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → M) : (s.toList.map f).sum = ∑ a ∈ s, f a := by
  rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_coe]
  congr 1
  rw [← Multiset.map_coe, Finset.coe_toList]

/-- The sum of the `single`-matrices in the top-right block of `Fin n ⊕ Fin n` is the
corresponding block matrix. -/
lemma sum_single_inl_inr_fromBlocks {R : Type*} [Semiring R] {n : ℕ}
    (X : Matrix (Fin n) (Fin n) R) :
    (∑ p : Fin n × Fin n,
        (Matrix.single (Sum.inl p.1) (Sum.inr p.2) (X p.1 p.2) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R))
      = Matrix.fromBlocks 0 X 0 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rw [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.single_apply]
    simp
  · rw [Matrix.sum_apply, Matrix.fromBlocks_apply₁₂, Finset.sum_eq_single (i, j)]
    · simp [Matrix.single_apply]
    · intro b _ hb
      rw [Matrix.single_apply]
      simp only [Sum.inl.injEq, Sum.inr.injEq]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Prod.ext h1 h2)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Matrix.sum_apply, Matrix.fromBlocks_apply₂₁]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.single_apply]
    simp
  · rw [Matrix.sum_apply, Matrix.fromBlocks_apply₂₂]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.single_apply]
    simp

/-- The sum of the `single`-matrices in the bottom-left block of `Fin n ⊕ Fin n` is the
corresponding block matrix. -/
lemma sum_single_inr_inl_fromBlocks {R : Type*} [Semiring R] {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) R) :
    (∑ p : Fin n × Fin n,
        (Matrix.single (Sum.inr p.1) (Sum.inl p.2) (Y p.1 p.2) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R))
      = Matrix.fromBlocks 0 0 Y 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rw [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.single_apply]
    simp
  · rw [Matrix.sum_apply, Matrix.fromBlocks_apply₁₂]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.single_apply]
    simp
  · rw [Matrix.sum_apply, Matrix.fromBlocks_apply₂₁, Finset.sum_eq_single (i, j)]
    · simp [Matrix.single_apply]
    · intro b _ hb
      rw [Matrix.single_apply]
      simp only [Sum.inr.injEq, Sum.inl.injEq]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Prod.ext h1 h2)
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Matrix.sum_apply, Matrix.fromBlocks_apply₂₂]
    apply Finset.sum_eq_zero
    intro p _
    rw [Matrix.single_apply]
    simp

/-- `Matrix.reindex` sends `single i j a` to `single (e i) (e j) a`. -/
lemma reindex_single {R : Type*} [Zero R] {m p : Type*} [DecidableEq m] [DecidableEq p]
    (e : m ≃ p) (i j : m) (a : R) :
    Matrix.reindex e e (Matrix.single i j a) = Matrix.single (e i) (e j) a := by
  ext k l
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single_apply,
    Equiv.eq_symm_apply, eq_comm]

end Whitehead
end Work.KT
