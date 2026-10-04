import Mathlib
import Submission.Work.Diff.Alg.PA.CS_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Componentwise bound on Hamilton's quadratic term `Q`

The target of this file is the crude componentwise estimate

`|Q A i j k l| ≤ 5 n² |A|²`

for an arbitrary 4-index array `A : Curv4 n` (no `IsAlgCurv` hypothesis is needed: the bound is a
pure Cauchy–Schwarz estimate on the three quadratic sums defining `Q`).

Write `Q A i j k l = ∑ p ∑ q (T₁ + 2 T₂ - 2 T₃)` with
`T₁ = A i j p q · A k l p q`, `T₂ = A i p k q · A j p l q`, `T₃ = A i p l q · A j p k q`.
By Cauchy–Schwarz each of `∑|T₁|`, `∑|T₂|`, `∑|T₃|` is at most `|A|² = frobSq A`
(the relevant partial sums of squares are subsums of the full Frobenius square), so
`|Q A i j k l| ≤ 5 frobSq A ≤ 5 n² frobSq A` — the last step because `i : Fin n` gives `n ≥ 1`.

This is the analytic estimate behind the `PA` contract: the reaction term is at most quadratic in
the curvature, with a constant that only involves the dimension.
-/

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary absolute-value and Cauchy–Schwarz tools -/

/-- `|a + b - c| ≤ |a| + |b| + |c|`. -/
lemma abs_add_sub_le (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  have h1 : |a + b - c| ≤ |a + b| + |c| := by simpa using abs_sub (a + b) c
  have h2 : |a + b| ≤ |a| + |b| := abs_add_le a b
  linarith

/-- Cauchy–Schwarz for a double sum of absolute values. -/
lemma sum2_abs_mul_le (f g : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, |f p q| * |g p q|) ≤
      Real.sqrt (∑ p, ∑ q, f p q ^ 2) * Real.sqrt (∑ p, ∑ q, g p q ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n × Fin n))
    (fun x : Fin n × Fin n => |f x.1 x.2|) (fun x : Fin n × Fin n => |g x.1 x.2|)
  simpa only [Fintype.sum_prod_type, sq_abs] using h

/-- Cauchy–Schwarz in the form used below: if both partial sums of squares are dominated by
`frobSq A`, then so is the sum of the absolute products. -/
lemma sum_abs_mul_le_frobSq (A : Curv4 n) (f g : Fin n → Fin n → ℝ)
    (hf : (∑ p, ∑ q, f p q ^ 2) ≤ frobSq A) (hg : (∑ p, ∑ q, g p q ^ 2) ≤ frobSq A) :
    (∑ p, ∑ q, |f p q| * |g p q|) ≤ frobSq A := by
  refine le_trans (sum2_abs_mul_le f g) ?_
  have hle : Real.sqrt (∑ p, ∑ q, f p q ^ 2) * Real.sqrt (∑ p, ∑ q, g p q ^ 2)
      ≤ Real.sqrt (frobSq A) * Real.sqrt (frobSq A) :=
    mul_le_mul (Real.sqrt_le_sqrt hf) (Real.sqrt_le_sqrt hg)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [sqrt_frobSq_mul_self A] at hle
  exact hle

/-! ## Partial sums of squares are bounded by `frobSq` -/

/-- The partial sum over the last two indices, with the first two fixed, is at most `frobSq`. -/
lemma sum_sq_le_frobSq_ij (A : Curv4 n) (i j : Fin n) :
    (∑ p, ∑ q, A i j p q ^ 2) ≤ frobSq A := by
  have h1 : (∑ p, ∑ q, A i j p q ^ 2) ≤ ∑ j' : Fin n, ∑ k, ∑ l, A i j' k l ^ 2 :=
    Finset.single_le_sum (f := fun j' : Fin n => ∑ k, ∑ l, A i j' k l ^ 2)
      (fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h2 : (∑ j' : Fin n, ∑ k, ∑ l, A i j' k l ^ 2) ≤ frobSq A := by
    simp only [frobSq]
    exact Finset.single_le_sum (f := fun i' : Fin n => ∑ j', ∑ k, ∑ l, A i' j' k l ^ 2)
      (fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ =>
        Finset.sum_nonneg fun d _ => sq_nonneg _)
      (Finset.mem_univ i)
  exact le_trans h1 h2

/-- The partial sum over the indices `(2,4)` of a fixed pair `(i,l)` (or `(i,k)`) is at most
`frobSq`. -/
lemma sum_sq_le_frobSq_ipkq (A : Curv4 n) (i k : Fin n) :
    (∑ p, ∑ q, A i p k q ^ 2) ≤ frobSq A := by
  have h1 : (∑ p, ∑ q, A i p k q ^ 2) ≤ ∑ p : Fin n, ∑ k' : Fin n, ∑ q, A i p k' q ^ 2 := by
    apply Finset.sum_le_sum; intro p _
    exact Finset.single_le_sum (f := fun k' : Fin n => ∑ q, A i p k' q ^ 2)
      (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ k)
  have h2 : (∑ p : Fin n, ∑ k' : Fin n, ∑ q, A i p k' q ^ 2) ≤ frobSq A := by
    simp only [frobSq]
    exact Finset.single_le_sum (f := fun i' : Fin n => ∑ p, ∑ k', ∑ q, A i' p k' q ^ 2)
      (fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ =>
        Finset.sum_nonneg fun d _ => sq_nonneg _)
      (Finset.mem_univ i)
  exact le_trans h1 h2

/-! ## The bound `|Q A i j k l| ≤ 5 |A|²` -/

/-- The crude componentwise bound on `Q`, with the constant `5` (which is stronger than the
`5 n²` of the target statement). -/
lemma Q_comp_le_frobSq (A : Curv4 n) (i j k l : Fin n) : |Q A i j k l| ≤ 5 * frobSq A := by
  have h1 : (∑ p, ∑ q, |A i j p q| * |A k l p q|) ≤ frobSq A :=
    sum_abs_mul_le_frobSq A _ _ (sum_sq_le_frobSq_ij A i j) (sum_sq_le_frobSq_ij A k l)
  have h2 : (∑ p, ∑ q, |A i p k q| * |A j p l q|) ≤ frobSq A :=
    sum_abs_mul_le_frobSq A _ _ (sum_sq_le_frobSq_ipkq A i k) (sum_sq_le_frobSq_ipkq A j l)
  have h3 : (∑ p, ∑ q, |A i p l q| * |A j p k q|) ≤ frobSq A :=
    sum_abs_mul_le_frobSq A _ _ (sum_sq_le_frobSq_ipkq A i l) (sum_sq_le_frobSq_ipkq A j k)
  have e2 : (∑ p, ∑ q, |2 * A i p k q * A j p l q|)
      = 2 * (∑ p, ∑ q, |A i p k q| * |A j p l q|) := by
    have hp : ∀ p q, |2 * A i p k q * A j p l q| = 2 * (|A i p k q| * |A j p l q|) := by
      intro p q
      rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]; ring
    simp only [hp]
    rw [Finset.mul_sum]
    simp only [Finset.mul_sum]
  have e3 : (∑ p, ∑ q, |2 * A i p l q * A j p k q|)
      = 2 * (∑ p, ∑ q, |A i p l q| * |A j p k q|) := by
    have hp : ∀ p q, |2 * A i p l q * A j p k q| = 2 * (|A i p l q| * |A j p k q|) := by
      intro p q
      rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]; ring
    simp only [hp]
    rw [Finset.mul_sum]
    simp only [Finset.mul_sum]
  have ht1 : (∑ p, ∑ q, |A i j p q * A k l p q|) ≤ frobSq A := by
    simpa only [abs_mul] using h1
  have ht2 : (∑ p, ∑ q, |2 * A i p k q * A j p l q|) ≤ 2 * frobSq A := by
    rw [e2]; exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  have ht3 : (∑ p, ∑ q, |2 * A i p l q * A j p k q|) ≤ 2 * frobSq A := by
    rw [e3]; exact mul_le_mul_of_nonneg_left h3 (by norm_num)
  have hQ : |Q A i j k l| ≤ ∑ p, ∑ q, (|A i j p q * A k l p q| + |2 * A i p k q * A j p l q|
      + |2 * A i p l q * A j p k q|) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    apply Finset.sum_le_sum; intro p _
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    apply Finset.sum_le_sum; intro q _
    exact abs_add_sub_le _ _ _
  have hsplit : (∑ p, ∑ q, (|A i j p q * A k l p q| + |2 * A i p k q * A j p l q|
      + |2 * A i p l q * A j p k q|))
      = (∑ p, ∑ q, |A i j p q * A k l p q|) + (∑ p, ∑ q, |2 * A i p k q * A j p l q|)
        + (∑ p, ∑ q, |2 * A i p l q * A j p k q|) := by
    simp only [Finset.sum_add_distrib]
  calc |Q A i j k l| ≤ ∑ p, ∑ q, (|A i j p q * A k l p q| + |2 * A i p k q * A j p l q|
        + |2 * A i p l q * A j p k q|) := hQ
    _ = (∑ p, ∑ q, |A i j p q * A k l p q|) + (∑ p, ∑ q, |2 * A i p k q * A j p l q|)
        + (∑ p, ∑ q, |2 * A i p l q * A j p k q|) := hsplit
    _ ≤ frobSq A + 2 * frobSq A + 2 * frobSq A := by linarith [ht1, ht2, ht3]
    _ = 5 * frobSq A := by ring

/-! ## The target statement -/

theorem Q_comp_abs_le (n : ℕ) (A : _root_.Submission.Diff.Alg.Curv4 n) (i j k l : Fin n) :
    |_root_.Submission.Diff.Alg.Q A i j k l| ≤
      5 * (n : ℝ) ^ 2 * _root_.Submission.Diff.Alg.frobSq A := by
  have hn : (1 : ℝ) ≤ (n : ℝ) := by
    have h : 0 < n := i.pos
    exact_mod_cast h
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hc : 0 ≤ frobSq A := frobSq_nonneg A
  calc |Q A i j k l| ≤ 5 * frobSq A := Q_comp_le_frobSq A i j k l
    _ ≤ 5 * (n : ℝ) ^ 2 * frobSq A := by nlinarith

end Work.Diff.Alg.PA
