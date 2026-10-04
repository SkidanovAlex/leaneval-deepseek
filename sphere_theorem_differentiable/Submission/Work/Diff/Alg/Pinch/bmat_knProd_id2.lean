import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `bmat` of the Kulkarni–Nomizu product `A ∧ id`

Contraction identity for the two-vector matrix `bmat v R p q = ∑ᵢⱼ vᵢ vⱼ R i p j q` applied to
`R = A ∧ id₂`:

`(A ∧ id) v v p q = (∑ᵢⱼ vᵢ Aᵢⱼ vⱼ) δₚq − v_p ∑ⱼ A_qj vⱼ − v_q ∑ⱼ A_pj vⱼ + (∑ᵢ vᵢ²) A_pq`

for symmetric `A`.  This is the `(v, v)`-contraction of the linearisation of the Ricci tensor
along the `Ric₀ ∧ id` direction of the Böhm–Wilking transformation `ℓ_{a,b}`
(Brendle–Schoen §3, Böhm–Wilking Thm. 2); it is used to compute the quadratic form
`∑_{pq} (bmat v (A ∧ id)) p q · M p q` of the `Ric`-derivative of a reaction term.

The proof is a finite computation: expand `knProd` and contract the four Kronecker deltas with
the elementary summation lemmas `bkId2_delta_*` below.
-/

namespace Work.Diff.Alg.Pinch

open Finset

/-- `∑ j, f j · δ_{p j} = f p`. -/
private lemma bkId2_delta_right {n : ℕ} (f : Fin n → ℝ) (p : Fin n) :
    (∑ j, f j * (if p = j then (1 : ℝ) else 0)) = f p := by
  rw [show (∑ j, f j * (if p = j then (1 : ℝ) else 0)) = ∑ j, (if p = j then f j else 0) from by
    apply Finset.sum_congr rfl; intro j _; by_cases h : p = j <;> simp [h]]
  simp [Finset.sum_ite_eq]

/-- `∑ i ∑ j, f i j · δ_{p j} = ∑ i, f i p`. -/
private lemma bkId2_delta_right2 {n : ℕ} (f : Fin n → Fin n → ℝ) (p : Fin n) :
    (∑ i, ∑ j, f i j * (if p = j then (1 : ℝ) else 0)) = ∑ i, f i p := by
  apply Finset.sum_congr rfl; intro i _
  exact bkId2_delta_right (fun j => f i j) p

/-- `∑ i ∑ j, f i j · δ_{i q} = ∑ j, f q j`. -/
private lemma bkId2_delta_left2 {n : ℕ} (f : Fin n → Fin n → ℝ) (q : Fin n) :
    (∑ i, ∑ j, f i j * (if i = q then (1 : ℝ) else 0)) = ∑ j, f q j := by
  have h : ∀ i, (∑ j, f i j * (if i = q then (1 : ℝ) else 0))
      = (if i = q then (1 : ℝ) else 0) * (∑ j, f i j) := by
    intro i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  rw [show (∑ i, (if i = q then (1 : ℝ) else 0) * (∑ j, f i j))
      = ∑ i, (if i = q then (∑ j, f i j) else 0) from by
    apply Finset.sum_congr rfl; intro i _; by_cases hh : i = q <;> simp [hh]]
  simp [Finset.sum_ite_eq']

/-- `∑ i ∑ j, f i j · δ_{i j} = ∑ i, f i i`. -/
private lemma bkId2_delta_diag2 {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, f i j * (if i = j then (1 : ℝ) else 0)) = ∑ i, f i i := by
  apply Finset.sum_congr rfl; intro i _
  rw [show (∑ j, f i j * (if i = j then (1 : ℝ) else 0)) = ∑ j, (if i = j then f i j else 0) from by
    apply Finset.sum_congr rfl; intro j _; by_cases h : i = j <;> simp [h]]
  simp [Finset.sum_ite_eq]

/-- Pull a constant out of a double sum. -/
private lemma bkId2_mul_const2 {n : ℕ} (f : Fin n → Fin n → ℝ) (c : ℝ) :
    (∑ i, ∑ j, f i j * c) = (∑ i, ∑ j, f i j) * c := by
  simp only [Finset.sum_mul]

theorem bmat_knProd_id2 (n : ℕ) {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i)
    (v : Fin n → ℝ) (p q : Fin n) :
    Work.Diff.Alg.Pinch.bmat v (Work.Diff.Alg.Pinch.knProd A (Work.Diff.Alg.Pinch.id2 n)) p q
      = (∑ i, ∑ j, v i * A i j * v j) * (if p = q then 1 else 0)
        - v p * (∑ j, A q j * v j) - v q * (∑ j, A p j * v j)
        + (∑ i, v i * v i) * A p q := by
  simp only [bmat]
  -- Pointwise expansion: `(A ∧ id) i p j q = A i j δ_{p q} - A i q δ_{p j} - A p j δ_{i q} + A p q δ_{i j}`.
  have hterm : ∀ i j : Fin n, v i * v j * knProd A (id2 n) i p j q
      = (v i * v j * A i j) * (if p = q then (1 : ℝ) else 0)
        - (v i * v j * A i q) * (if p = j then (1 : ℝ) else 0)
        - (v i * v j * A p j) * (if i = q then (1 : ℝ) else 0)
        + (v i * v j * A p q) * (if i = j then (1 : ℝ) else 0) := by
    intro i j
    simp only [knProd, id2]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))]
  -- The four contracted pieces.
  have h1 : (∑ i, ∑ j, (v i * v j * A i j) * (if p = q then (1 : ℝ) else 0))
      = (∑ i, ∑ j, v i * A i j * v j) * (if p = q then (1 : ℝ) else 0) := by
    rw [bkId2_mul_const2]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have h2 : (∑ i, ∑ j, (v i * v j * A i q) * (if p = j then (1 : ℝ) else 0))
      = v p * (∑ j, A q j * v j) := by
    rw [bkId2_delta_right2]
    rw [show (∑ i, v i * v p * A i q) = v p * ∑ i, A q i * v i from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [hA i q]; ring]
  have h3 : (∑ i, ∑ j, (v i * v j * A p j) * (if i = q then (1 : ℝ) else 0))
      = v q * (∑ j, A p j * v j) := by
    rw [bkId2_delta_left2]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    ring
  have h4 : (∑ i, ∑ j, (v i * v j * A p q) * (if i = j then (1 : ℝ) else 0))
      = (∑ i, v i * v i) * A p q := by
    rw [bkId2_delta_diag2, ← Finset.sum_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2, h3, h4]

end Work.Diff.Alg.Pinch
