import Mathlib
import Submission.Work.Diff.Alg.Pinch.BWDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Hamilton's reaction term on a Kulkarni–Nomizu product

For a symmetric `2`-tensor `C` (an `n × n` matrix), the quadratic reaction term `Q` of the
Ricci flow, evaluated on the "Ricci-type" curvature tensor `C ∧ id` (`knProd C (id2 n)`), is

`Q (C ∧ id) = -2 · (C Cᵀ) ∧ id + (n - 2) · C ∧ C + 2 (tr C) · C ∧ id + |C|² · (id ∧ id)`

where `(C Cᵀ) i j = ∑ k, C i k * C j k` (`s2m C`), `tr C = ∑ i, C i i` (`trM C`) and
`|C|² = ∑ i j, C i j * C i j` (`frb C`).

This is the computation underlying Lemma 2.2 of Böhm–Wilking, *Manifolds with positive curvature
operators are space forms* (arXiv math/0606187), in the special case of a curvature tensor of
Ricci type; it is used in the proof of their Theorem 2 (the identity `D_{a,b}`).

## Proof

`Q (C ∧ id) i j k l` is the double sum of `T1 + 2 T2 - 2 T3` with

* `T1 = ∑ p q, (C ∧ id) i j p q · (C ∧ id) k l p q`,
* `T2 = ∑ p q, (C ∧ id) i p k q · (C ∧ id) j p l q`,
* `T3 = ∑ p q, (C ∧ id) i p l q · (C ∧ id) j p k q`.

Each is evaluated by expanding `knProd C id` (four terms) and applying the contraction lemmas of
`Work.Diff.Alg.Pinch.BWDefs` to the `16 = 4 × 4` products.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- Row shape of `s2m`, used to fold the sums produced by the contraction lemmas. -/
lemma sum_row_s2m (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    (∑ x, A i x * A j x) = s2m A i j := rfl

/-- The "row" and "column" descriptions of `s2m` agree for a symmetric matrix. -/
lemma sum_col_s2m {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) (i j : Fin n) :
    (∑ x, A x i * A x j) = s2m A i j := by
  simp only [s2m]
  apply Finset.sum_congr rfl; intro x _
  rw [hA x i, hA x j]

lemma sum_id2_id2' (a b : Fin n) : (∑ q, id2 n q a * id2 n q b) = id2 n a b := by
  rw [show (∑ q, id2 n q a * id2 n q b) = ∑ q, id2 n a q * id2 n b q from
    Finset.sum_congr rfl (fun q _ => by rw [id2_symm q a, id2_symm q b])]
  exact sum_id2_id2 a b

/-! ## The first double sum -/

lemma T1eval (n : ℕ) {C : Fin n → Fin n → ℝ} (hC : ∀ i j, C i j = C j i) (i j k l : Fin n) :
    (∑ p, ∑ q, (knProd C (id2 n)) i j p q * (knProd C (id2 n)) k l p q)
      = 2 * s2m C i k * id2 n j l - 2 * s2m C i l * id2 n j k - 2 * s2m C j k * id2 n i l
        + 2 * s2m C j l * id2 n i k + 4 * (C i k * C j l) - 4 * (C i l * C j k) := by
  have key : ∀ p q : Fin n, (knProd C (id2 n)) i j p q * (knProd C (id2 n)) k l p q
      = ((C i p * id2 n j q) * (C k p * id2 n l q))
        - ((C i p * id2 n j q) * (C k q * id2 n l p))
        - ((C i p * id2 n j q) * (C l p * id2 n k q))
        + ((C i p * id2 n j q) * (C l q * id2 n k p))
        - ((C i q * id2 n j p) * (C k p * id2 n l q))
        + ((C i q * id2 n j p) * (C k q * id2 n l p))
        + ((C i q * id2 n j p) * (C l p * id2 n k q))
        - ((C i q * id2 n j p) * (C l q * id2 n k p))
        - ((C j p * id2 n i q) * (C k p * id2 n l q))
        + ((C j p * id2 n i q) * (C k q * id2 n l p))
        + ((C j p * id2 n i q) * (C l p * id2 n k q))
        - ((C j p * id2 n i q) * (C l q * id2 n k p))
        + ((C j q * id2 n i p) * (C k p * id2 n l q))
        - ((C j q * id2 n i p) * (C k q * id2 n l p))
        - ((C j q * id2 n i p) * (C l p * id2 n k q))
        + ((C j q * id2 n i p) * (C l q * id2 n k p)) := by
    intro p q; simp only [knProd]; ring
  simp only [key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum2_pair₁, sum2_pair₂, sum2_pair₁, sum2_pair₂, sum2_pair₃, sum2_pair₄, sum2_pair₃,
    sum2_pair₄, sum2_pair₁, sum2_pair₂, sum2_pair₁, sum2_pair₂, sum2_pair₃, sum2_pair₄,
    sum2_pair₃, sum2_pair₄]
  simp only [sum_id2_id2, sum_id2_mul, sum_mul_id2']
  simp only [sum_row_s2m]
  rw [hC k j, hC l j, hC k i, hC l i]
  ring

/-! ## The second double sum -/

lemma T2eval (n : ℕ) {C : Fin n → Fin n → ℝ} (hC : ∀ i j, C i j = C j i) (i j k l : Fin n) :
    (∑ p, ∑ q, (knProd C (id2 n)) i p k q * (knProd C (id2 n)) j p l q)
      = ((n : ℝ) - 4) * (C i k * C j l)
        + trM C * (C i k * id2 n j l) + trM C * (C j l * id2 n i k)
        + s2m C i j * id2 n k l + s2m C k l * id2 n i j + 2 * (C i j * C k l)
        - 2 * (s2m C i k * id2 n j l) - 2 * (s2m C j l * id2 n i k)
        + frb C * (id2 n i k * id2 n j l) := by
  have key : ∀ p q : Fin n,
      (knProd C (id2 n)) i p k q * (knProd C (id2 n)) j p l q
      = ((C i k * id2 n p q) * (C j l * id2 n p q))
        - ((C i k * id2 n p q) * (C j q * id2 n p l))
        - ((C i k * id2 n p q) * (C p l * id2 n j q))
        + ((C i k * id2 n p q) * (C p q * id2 n j l))
        - ((C i q * id2 n p k) * (C j l * id2 n p q))
        + ((C i q * id2 n p k) * (C j q * id2 n p l))
        + ((C i q * id2 n p k) * (C p l * id2 n j q))
        - ((C i q * id2 n p k) * (C p q * id2 n j l))
        - ((C p k * id2 n i q) * (C j l * id2 n p q))
        + ((C p k * id2 n i q) * (C j q * id2 n p l))
        + ((C p k * id2 n i q) * (C p l * id2 n j q))
        - ((C p k * id2 n i q) * (C p q * id2 n j l))
        + ((C p q * id2 n i k) * (C j l * id2 n p q))
        - ((C p q * id2 n i k) * (C j q * id2 n p l))
        - ((C p q * id2 n i k) * (C p l * id2 n j q))
        + ((C p q * id2 n i k) * (C p q * id2 n j l)) := by
    intro p q; simp only [knProd]; ring
  simp only [key]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum2_diag₁, sum2_diag₂, sum2_diag₃, sum2_diag₄, sum2_diag₅, sum2_pair₄, sum2_pair₃,
    sum2_diag₇, sum2_diag₆, sum2_pair₂, sum2_pair₁, sum2_diag₈, sum2_diag₁₂, sum2_diag₉,
    sum2_diag₁₀, sum2_diag₁₁]
  simp only [sum_id2_id2, sum_id2_id2', sum_id2_mul, sum_mul_id2, sum_mul_id2', sum_id2_mul']
  simp only [sum_col_s2m hC, sum_row_s2m]
  rw [sum_s2m_diag, ← trM_eq]
  rw [s2m_symm (A := C) k i, s2m_symm (A := C) l j]
  rw [hC l k, hC j i]
  ring

/-! ## The third double sum -/

lemma T3eval (n : ℕ) {C : Fin n → Fin n → ℝ} (hC : ∀ i j, C i j = C j i) (i j k l : Fin n) :
    (∑ p, ∑ q, (knProd C (id2 n)) i p l q * (knProd C (id2 n)) j p k q)
      = ((n : ℝ) - 4) * (C i l * C j k)
        + trM C * (C i l * id2 n j k) + trM C * (C j k * id2 n i l)
        + s2m C i j * id2 n k l + s2m C k l * id2 n i j + 2 * (C i j * C k l)
        - 2 * (s2m C i l * id2 n j k) - 2 * (s2m C j k * id2 n i l)
        + frb C * (id2 n i l * id2 n j k) := by
  rw [T2eval n hC i j l k]
  rw [id2_symm l k, s2m_symm (A := C) l k, hC l k]

/-! ## The identity -/

theorem Q_knProd_apply (n : ℕ) {C : Fin n → Fin n → ℝ} (hC : ∀ i j, C i j = C j i) :
    Submission.Diff.Alg.Q (knProd C (id2 n))
      = (-2 : ℝ) • knProd (s2m C) (id2 n)
        + ((n : ℝ) - 2) • knProd C C
        + (2 * trM C) • knProd C (id2 n)
        + (frb C) • knProd (id2 n) (id2 n) := by
  funext i j k l
  have hQ : Submission.Diff.Alg.Q (knProd C (id2 n)) i j k l
      = (∑ p, ∑ q, (knProd C (id2 n)) i j p q * (knProd C (id2 n)) k l p q)
        + 2 * (∑ p, ∑ q, (knProd C (id2 n)) i p k q * (knProd C (id2 n)) j p l q)
        - 2 * (∑ p, ∑ q, (knProd C (id2 n)) i p l q * (knProd C (id2 n)) j p k q) := by
    simp only [Submission.Diff.Alg.Q]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rw [hQ, T1eval n hC i j k l, T2eval n hC i j k l, T3eval n hC i j k l]
  simp only [knProd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Work.Diff.Alg.Pinch
