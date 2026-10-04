import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Double contraction of `A ∧ id` against a pair of vectors

For a symmetric matrix `A` and the identity `2`-tensor `id2 n` (the Kronecker delta `δ`), the
four-fold contraction of the Kulkarni–Nomizu product `A ∧ δ` against a pair of vectors `v` is

`∑ᵢⱼ (A ∧ δ)_{i p j q} vᵢ vⱼ
   = (∑ᵢⱼ Aᵢⱼ vᵢ vⱼ) δ_{pq} − (A v)q v_p − (A v)_p v_q + |v|² A_{pq}`.

This is the algebraic identity behind the second variation of the `ℓ`-transform: it lets one read
off the purely `Ric`-type contribution of a term `b · ric₀ ∧ id` when contracted against `v ⊗ v`.

The proof is a direct expansion: `(A ∧ δ)_{i p j q} = Aᵢⱼ δ_{pq} − A_{iq} δ_{pj} − A_{pj} δ_{iq} +
A_{pq} δ_{ij}` (with the indices of the four slots of `knProd` as in `Defs`), and each of the four
resulting sums is a single Kronecker contraction. Symmetry of `A` is used only to rewrite
`∑ᵢ A_{iq} vᵢ` as `∑ᵢ A_{qi} vᵢ`.
-/

namespace Work.Diff.Alg.Pinch

open Finset

variable {n : ℕ}

/-- `∑ᵢ ∑ⱼ δ_{pq} (Aᵢⱼ vᵢ vⱼ) = (∑ᵢ ∑ⱼ Aᵢⱼ vᵢ vⱼ) · δ_{pq}`. -/
lemma sum_sum_delta_const (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (p q : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n, (if p = q then (1 : ℝ) else 0) * (A i j * v i * v j))
      = (∑ i : Fin n, ∑ j : Fin n, A i j * v i * v j) * (if p = q then (1 : ℝ) else 0) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _
  ring

/-- `∑ᵢ ∑ⱼ δ_{pj} (A_{iq} vᵢ vⱼ) = (∑ᵢ A_{iq} vᵢ) · v_p`. -/
lemma sum_sum_delta_right (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (p q : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n, (if p = j then (1 : ℝ) else 0) * (A i q * v i * v j))
      = (∑ i : Fin n, A i q * v i) * v p := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- `∑ᵢ ∑ⱼ δ_{iq} (A_{pj} vᵢ vⱼ) = (∑ⱼ A_{pj} vⱼ) · v_q`. -/
lemma sum_sum_delta_left (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (p q : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n, (if i = q then (1 : ℝ) else 0) * (A p j * v i * v j))
      = (∑ j : Fin n, A p j * v j) * v q := by
  have h1 : ∀ i : Fin n, (∑ j : Fin n, (if i = q then (1 : ℝ) else 0) * (A p j * v i * v j))
      = (if i = q then (1 : ℝ) else 0) * v i * (∑ j : Fin n, A p j * v j) := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [← Finset.sum_mul]
  have h2 : (∑ i : Fin n, (if i = q then (1 : ℝ) else 0) * v i) = v q := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp
  rw [h2]
  ring

/-- `∑ᵢ ∑ⱼ δ_{ij} (A_{pq} vᵢ vⱼ) = A_{pq} · ∑ᵢ vᵢ vᵢ`. -/
lemma sum_sum_delta_diag (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (p q : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) * (A p q * v i * v j))
      = A p q * (∑ i : Fin n, v i * v i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp
  ring

theorem knProd_id2_contraction (n : ℕ) {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i)
    (v : Fin n → ℝ) (p q : Fin n) :
    (∑ i, ∑ j, Work.Diff.Alg.Pinch.knProd A (Work.Diff.Alg.Pinch.id2 n) i p j q * v i * v j)
      = (∑ i, ∑ j, A i j * v i * v j) * (if p = q then (1 : ℝ) else 0)
        - (∑ i, A q i * v i) * v p - (∑ i, A p i * v i) * v q
        + (∑ i, v i * v i) * A p q := by
  classical
  -- Step 1: expand `(A ∧ δ)_{i p j q}` into its four Kronecker terms.
  have hterm : ∀ i j : Fin n, knProd A (id2 n) i p j q
      = A i j * (if p = q then (1 : ℝ) else 0) - A i q * (if p = j then (1 : ℝ) else 0)
        - A p j * (if i = q then (1 : ℝ) else 0) + A p q * (if i = j then (1 : ℝ) else 0) := by
    intro i j; simp only [knProd, id2]
  simp only [hterm]
  -- Step 2: distribute the product `· v i · v j` over the four terms.
  have hsplit : ∀ i j : Fin n,
      (A i j * (if p = q then (1 : ℝ) else 0) - A i q * (if p = j then (1 : ℝ) else 0)
        - A p j * (if i = q then (1 : ℝ) else 0) + A p q * (if i = j then (1 : ℝ) else 0))
        * v i * v j
      = (if p = q then (1 : ℝ) else 0) * (A i j * v i * v j)
        - (if p = j then (1 : ℝ) else 0) * (A i q * v i * v j)
        - (if i = q then (1 : ℝ) else 0) * (A p j * v i * v j)
        + (if i = j then (1 : ℝ) else 0) * (A p q * v i * v j) := by
    intro i j; ring
  -- Step 3: rewrite `∑ᵢ A_{iq} vᵢ` by symmetry of `A`.
  have hsum : (∑ i : Fin n, A i q * v i) = ∑ i : Fin n, A q i * v i := by
    apply Finset.sum_congr rfl; intro i _
    rw [hA i q]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_sum_delta_const, sum_sum_delta_right, sum_sum_delta_left, sum_sum_delta_diag, hsum]
  ring

end Work.Diff.Alg.Pinch
