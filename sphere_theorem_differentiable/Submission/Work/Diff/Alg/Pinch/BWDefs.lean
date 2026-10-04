import Mathlib
import Submission.Work.Diff.Alg.Pinch.BQDefs
import Submission.Work.Diff.Alg.Pinch.ric_Q
import Submission.Work.Diff.Alg.Pinch.scalAlg_Q
import Submission.Work.Diff.Alg.Pinch.ric_knProd_id2
import Submission.Work.Diff.Alg.Pinch.scalAlg_knProd
import Submission.Work.Diff.Alg.Pinch.ell_isAlgCurv
import Submission.Work.Diff.Alg.Pinch.rot_knProd_id2
import Submission.Work.Diff.Alg.Pinch.Q_isAlgCurv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Tensor calculus for the Böhm–Wilking identity

Definitions and index-contraction lemmas used in the proof of the Böhm–Wilking identity
(Böhm–Wilking, *Manifolds with positive curvature operators are space forms*, Theorem 2):

`linv a b (Q (ell a b R)) = Q R + D_{a,b}(R)`.

## The `A`-forms

For a symmetric `2`-tensor `A` (an `n × n` matrix) we write

* `s2m A i j = ∑ k, A i k * A j k`   (the product `A Aᵀ`, i.e. `A²` for symmetric `A`),
* `trM A = ∑ i, A i i`,
* `frb A = ∑ i, ∑ j, A i j * A i j`.

Every expression met in the expansion of `Q (knProd A id)` is a sum of products of at most two
factors `A x y` and Kronecker deltas `id2 n x y`.  The lemmas below evaluate all the double sums
`∑ p, ∑ q, ...` that occur:  the four "separated" shapes (`sum2_canon₁`–`sum2_canon₄`) and the
shapes containing a diagonal factor `id2 n p q` (`sum2_diag₁`–`sum2_diag₁₂`).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## The `A`-forms -/

/-- Row-row product of a matrix: `s2m A i j = ∑ k, A i k * A j k`.  For symmetric `A` this is the
matrix square (see `s2m_rows`). -/
noncomputable def s2m (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ := fun i j => ∑ k, A i k * A j k

/-- Trace of a matrix. -/
noncomputable def trM (A : Fin n → Fin n → ℝ) : ℝ := ∑ i, A i i

/-- Squared Frobenius norm of a matrix. -/
noncomputable def frb (A : Fin n → Fin n → ℝ) : ℝ := ∑ i, ∑ j, A i j * A i j

lemma s2m_symm {A : Fin n → Fin n → ℝ} (i j : Fin n) : s2m A i j = s2m A j i := by
  simp only [s2m]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- For a symmetric matrix the row-row product is the matrix square. -/
lemma s2m_rows {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i) (i j : Fin n) :
    s2m A i j = ∑ k, A i k * A k j := by
  simp only [s2m]
  exact Finset.sum_congr rfl (fun k _ => by rw [hA j k])

lemma sum_s2m_diag (A : Fin n → Fin n → ℝ) : (∑ i, s2m A i i) = frb A := by
  simp only [s2m, frb]

lemma trM_eq {A : Fin n → Fin n → ℝ} : trM A = ∑ i, A i i := rfl

lemma frb_eq {A : Fin n → Fin n → ℝ} : frb A = ∑ i, ∑ j, A i j * A i j := rfl

/-! ## Kronecker-delta contractions -/

lemma sum_id2_mul (f : Fin n → ℝ) (a : Fin n) : (∑ q, id2 n a q * f q) = f a := by
  simp only [id2]
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [show ¬ (a = c) from fun h => hc h.symm]
  · intro h; exact absurd (Finset.mem_univ a) h

lemma sum_mul_id2 (f : Fin n → ℝ) (a : Fin n) : (∑ q, f q * id2 n q a) = f a := by
  simp only [id2]
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [show ¬ (c = a) from hc]
  · intro h; exact absurd (Finset.mem_univ a) h

lemma sum_mul_id2' (f : Fin n → ℝ) (a : Fin n) : (∑ q, f q * id2 n a q) = f a := by
  rw [show (∑ q, f q * id2 n a q) = ∑ q, f q * id2 n q a from
    Finset.sum_congr rfl (fun q _ => by rw [id2_symm])]
  exact sum_mul_id2 f a

lemma sum_id2_mul' (f : Fin n → ℝ) (a : Fin n) : (∑ q, id2 n q a * f q) = f a := by
  rw [show (∑ q, id2 n q a * f q) = ∑ q, id2 n a q * f q from
    Finset.sum_congr rfl (fun q _ => by rw [id2_symm])]
  exact sum_id2_mul f a

lemma sum_id2_id2 (a b : Fin n) : (∑ q, id2 n a q * id2 n b q) = id2 n a b := by
  rw [sum_id2_mul (fun q => id2 n b q) a]
  exact id2_symm b a

/-! ## Separated shapes -/

lemma sum2_canon₁ (a b c d : Fin n → ℝ) :
    (∑ p, ∑ q, a p * b q * c p * d q) = (∑ p, a p * c p) * (∑ q, b q * d q) := by
  trans (∑ p, (a p * c p) * (∑ q, b q * d q))
  · apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  · rw [Finset.sum_mul]

lemma sum2_canon₂ (a b c d : Fin n → ℝ) :
    (∑ p, ∑ q, a p * b q * c q * d p) = (∑ p, a p * d p) * (∑ q, b q * c q) := by
  trans (∑ p, (a p * d p) * (∑ q, b q * c q))
  · apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  · rw [Finset.sum_mul]

lemma sum2_canon₃ (a b c d : Fin n → ℝ) :
    (∑ p, ∑ q, a q * b p * c p * d q) = (∑ p, b p * c p) * (∑ q, a q * d q) := by
  trans (∑ p, (b p * c p) * (∑ q, a q * d q))
  · apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  · rw [Finset.sum_mul]

lemma sum2_canon₄ (a b c d : Fin n → ℝ) :
    (∑ p, ∑ q, a q * b p * c q * d p) = (∑ p, b p * d p) * (∑ q, a q * c q) := by
  trans (∑ p, (b p * d p) * (∑ q, a q * c q))
  · apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  · rw [Finset.sum_mul]

/-! ## Shapes with a diagonal factor `id2 n p q` -/

lemma sum2_diag₁ (x y : ℝ) :
    (∑ p, ∑ q, (x * id2 n p q) * (y * id2 n p q)) = x * y * (n : ℝ) := by
  trans (∑ _p : Fin n, x * y * 1)
  · apply Finset.sum_congr rfl; intro p _
    trans (x * y * (∑ q, id2 n p q * id2 n p q))
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _; ring
    · rw [sum_id2_id2]
      have h1 : id2 n p p = (1 : ℝ) := by simp [id2]
      rw [h1, mul_one]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma sum2_diag₂ (x : ℝ) (a b : Fin n → ℝ) :
    (∑ p, ∑ q, (x * id2 n p q) * (a q * b p)) = x * ∑ p, a p * b p := by
  trans (∑ p, (x * b p) * (∑ q, id2 n p q * a q))
  · apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  · simp only [sum_id2_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _; ring

lemma sum2_diag₃ (x : ℝ) (a b : Fin n → ℝ) :
    (∑ p, ∑ q, (x * id2 n p q) * (a p * b q)) = x * ∑ p, a p * b p := by
  trans (∑ p, (x * a p) * (∑ q, id2 n p q * b q))
  · apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  · simp only [sum_id2_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _; ring

lemma sum2_diag₄ (x y : ℝ) (a : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, (x * id2 n p q) * (a p q * y)) = x * y * ∑ p, a p p := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  trans (x * y * (∑ q, id2 n p q * a p q))
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  · rw [sum_id2_mul]

lemma sum2_diag₅ (x : ℝ) (a b : Fin n → ℝ) :
    (∑ p, ∑ q, (a q * b p) * (x * id2 n p q)) = x * ∑ p, a p * b p := by
  trans (∑ p, (x * b p) * (∑ q, a q * id2 n p q))
  · apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  · simp only [sum_mul_id2']
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _; ring

lemma sum2_diag₆ (x : ℝ) (a b : Fin n → ℝ) :
    (∑ p, ∑ q, (a p * b q) * (x * id2 n p q)) = x * ∑ p, a p * b p := by
  trans (∑ p, (x * a p) * (∑ q, b q * id2 n p q))
  · apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  · simp only [sum_mul_id2']
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _; ring

lemma sum2_diag₁₂ (x y : ℝ) (a : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, (a p q * y) * (x * id2 n p q)) = x * y * ∑ p, a p p := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  trans (x * y * (∑ q, a p q * id2 n p q))
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  · rw [sum_mul_id2']

/-! ## Mixed shapes with a *fixed* index in the delta -/

lemma sum2_diag₇ (m : Fin n) (y : ℝ) (a : Fin n → ℝ) (c : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, (a q * id2 n p m) * (c p q * y)) = y * ∑ q, a q * c m q := by
  trans (∑ q, (y * a q) * (∑ p, id2 n p m * c p q))
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro q _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _; ring
  · simp only [sum_id2_mul']
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring

lemma sum2_diag₈ (i : Fin n) (y : ℝ) (a : Fin n → ℝ) (c : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, (a p * id2 n i q) * (c p q * y)) = y * ∑ p, a p * c p i := by
  trans (∑ p, (y * a p) * (∑ q, id2 n i q * c p q))
  · apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  · simp only [sum_id2_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _; ring

lemma sum2_diag₉ (l : Fin n) (y : ℝ) (a : Fin n → Fin n → ℝ) (c : Fin n → ℝ) :
    (∑ p, ∑ q, (a p q * y) * (c q * id2 n p l)) = y * ∑ q, a l q * c q := by
  trans (∑ q, (y * c q) * (∑ p, a p q * id2 n p l))
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro q _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _; ring
  · simp only [sum_mul_id2]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring

lemma sum2_diag₁₀ (j : Fin n) (y : ℝ) (a : Fin n → Fin n → ℝ) (c : Fin n → ℝ) :
    (∑ p, ∑ q, (a p q * y) * (c p * id2 n j q)) = y * ∑ p, a p j * c p := by
  trans (∑ p, (y * c p) * (∑ q, a p q * id2 n j q))
  · apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  · simp only [sum_mul_id2']
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _; ring

lemma sum2_diag₁₁ (y y' : ℝ) (a c : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, (a p q * y) * (c p q * y')) = y * y' * (∑ p, ∑ q, a p q * c p q) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro q _; ring

/-! ## Paired (grouped) shapes

The same contractions, with the two factors of the *curvature* product kept grouped
`(a p * b q) * (c p * d q)`; these are the shapes produced by expanding
`knProd A (id2 n) x y p q * knProd A (id2 n) z w p q`. -/

lemma sum2_pair₁ (a b c d : Fin n → ℝ) :
    (∑ p, ∑ q, (a p * b q) * (c p * d q)) = (∑ p, a p * c p) * (∑ q, b q * d q) := by
  simpa only [mul_assoc] using sum2_canon₁ a b c d

lemma sum2_pair₂ (a b c d : Fin n → ℝ) :
    (∑ p, ∑ q, (a p * b q) * (c q * d p)) = (∑ p, a p * d p) * (∑ q, b q * c q) := by
  simpa only [mul_assoc] using sum2_canon₂ a b c d

lemma sum2_pair₃ (a b c d : Fin n → ℝ) :
    (∑ p, ∑ q, (a q * b p) * (c p * d q)) = (∑ p, b p * c p) * (∑ q, a q * d q) := by
  simpa only [mul_assoc] using sum2_canon₃ a b c d

lemma sum2_pair₄ (a b c d : Fin n → ℝ) :
    (∑ p, ∑ q, (a q * b p) * (c q * d p)) = (∑ p, b p * d p) * (∑ q, a q * c q) := by
  simpa only [mul_assoc] using sum2_canon₄ a b c d

/-! ## Sums over the whole index set -/

lemma sum_id2_id2'' (a b : Fin n) : (∑ q, id2 n a q * id2 n q b) = id2 n a b := by
  rw [show (∑ q, id2 n a q * id2 n q b) = ∑ q, id2 n a q * id2 n b q from
    Finset.sum_congr rfl (fun q _ => by rw [id2_symm q b])]
  exact sum_id2_id2 a b

lemma sum_id2_self (i : Fin n) : (∑ j, id2 n i j * id2 n i j) = (1 : ℝ) := by
  have := sum_id2_id2 (n := n) i i
  simpa [id2] using this

lemma sum_sum_id2_id2 : (∑ i, ∑ j, id2 n i j * id2 n i j) = (n : ℝ) := by
  simp only [sum_id2_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]

lemma sum_sum_id2_C (C : Fin n → Fin n → ℝ) : (∑ i, ∑ j, id2 n i j * C i j) = trM C := by
  simp only [trM]
  apply Finset.sum_congr rfl; intro i _
  exact sum_id2_mul (fun j => C i j) i

lemma sum_sum_C_id2 (C : Fin n → Fin n → ℝ) : (∑ i, ∑ j, C i j * id2 n i j) = trM C := by
  simp only [trM]
  apply Finset.sum_congr rfl; intro i _
  exact sum_mul_id2' (fun j => C i j) i

lemma sum_sum_const (c : ℝ) (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, c * f i j) = c * ∑ i, ∑ j, f i j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]

end Work.Diff.Alg.Pinch
