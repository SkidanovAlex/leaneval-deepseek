import Mathlib
import Submission.Work.Diff.Alg.PA.CS_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cauchy–Schwarz for the Frobenius pairing of curvature arrays

`tpair n A B = ∑ᵢⱼₖₗ Aᵢⱼₖₗ Bᵢⱼₖₗ` is the (Euclidean) Frobenius pairing of two 4-index arrays and
`frobSq A = ∑ᵢⱼₖₗ Aᵢⱼₖₗ²` is the squared Frobenius norm.  The pairing is bilinear, so the
Cauchy–Schwarz inequality `⟪A,B⟫ ≤ |A| |B|` holds for *arbitrary* arrays (no algebraic curvature
symmetry is needed): flatten the quadruple index `(i,j,k,l)` into a single index and apply the
finite-dimensional Cauchy–Schwarz inequality.
-/

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- Cauchy–Schwarz (absolute value form) for real finite sums:
`|∑ᵢ aᵢ bᵢ| ≤ √(∑ᵢ aᵢ²) · √(∑ᵢ bᵢ²)`.  Obtained by squaring
(`Finset.sum_mul_sq_le_sq_mul_sq`), taking square roots (`Real.sqrt_le_sqrt`), and splitting
`√(XY) = √X √Y`. -/
lemma abs_sum_mul_le_sqrt {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    |∑ i, a i * b i| ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
  have hsq : (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  calc |∑ i, a i * b i| = Real.sqrt ((∑ i, a i * b i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, a i ^ 2) * (∑ i, b i ^ 2)) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) :=
        Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _) _

theorem tpair_abs_le (n : ℕ) (A B : _root_.Submission.Diff.Alg.Curv4 n) :
    |_root_.Work.Diff.Alg.PA.tpair n A B| ≤ Real.sqrt (_root_.Submission.Diff.Alg.frobSq A) *
      Real.sqrt (_root_.Submission.Diff.Alg.frobSq B) := by
  -- flatten the quadruple index into `(Fin n × Fin n) × (Fin n × Fin n)`
  have htp : tpair n A B = ∑ p : (Fin n × Fin n) × (Fin n × Fin n),
      A p.1.1 p.1.2 p.2.1 p.2.2 * B p.1.1 p.1.2 p.2.1 p.2.2 := by
    simp only [tpair, Fintype.sum_prod_type]
  have hfA : frobSq A = ∑ p : (Fin n × Fin n) × (Fin n × Fin n),
      (A p.1.1 p.1.2 p.2.1 p.2.2) ^ 2 := by
    simp only [frobSq, Fintype.sum_prod_type]
  have hfB : frobSq B = ∑ p : (Fin n × Fin n) × (Fin n × Fin n),
      (B p.1.1 p.1.2 p.2.1 p.2.2) ^ 2 := by
    simp only [frobSq, Fintype.sum_prod_type]
  rw [htp, hfA, hfB]
  exact abs_sum_mul_le_sqrt _ _

end Work.Diff.Alg.PA
