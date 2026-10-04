import Mathlib
import Submission.Work.Diff.Alg.PA.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary toolkit for `Work.Diff.Alg.PA.CS_bounds`

Elementary estimates on the Frobenius square `frobSq` of a 4-index array and on sums of
products: the single-component bound `|X i j k l| ≤ √(|X|²)`, the arithmetic of constant
sums over `Fin n`, and the conversion of a componentwise bound into a bound on `frobSq`.

These are the tools with which the reaction term `Q` and its polarisation `Qbil` are bounded
by the Frobenius norm of the tensor.
-/

namespace Work.Diff.Alg.PA

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## `frobSq` basics -/

lemma frobSq_nonneg (X : Curv4 n) : 0 ≤ frobSq X := by
  simp only [frobSq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun l _ => sq_nonneg _

/-- `frobSq` is monotone in the sense of a single component: every squared component is at most
the total sum of squares. -/
lemma sq_apply_le_frobSq (X : Curv4 n) (i j k l : Fin n) : (X i j k l) ^ 2 ≤ frobSq X := by
  simp only [frobSq]
  have s1 : X i j k l ^ 2 ≤ ∑ l' : Fin n, X i j k l' ^ 2 :=
    Finset.single_le_sum (f := fun l' : Fin n => X i j k l' ^ 2)
      (fun a _ => sq_nonneg _) (Finset.mem_univ l)
  have s2 : (∑ l' : Fin n, X i j k l' ^ 2) ≤ ∑ k' : Fin n, ∑ l' : Fin n, X i j k' l' ^ 2 :=
    Finset.single_le_sum (f := fun k' : Fin n => ∑ l' : Fin n, X i j k' l' ^ 2)
      (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ k)
  have s3 : (∑ k' : Fin n, ∑ l' : Fin n, X i j k' l' ^ 2) ≤
      ∑ j' : Fin n, ∑ k' : Fin n, ∑ l' : Fin n, X i j' k' l' ^ 2 :=
    Finset.single_le_sum (f := fun j' : Fin n => ∑ k' : Fin n, ∑ l' : Fin n, X i j' k' l' ^ 2)
      (fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ => sq_nonneg _)
      (Finset.mem_univ j)
  have s4 : (∑ j' : Fin n, ∑ k' : Fin n, ∑ l' : Fin n, X i j' k' l' ^ 2) ≤
      ∑ i' : Fin n, ∑ j' : Fin n, ∑ k' : Fin n, ∑ l' : Fin n, X i' j' k' l' ^ 2 :=
    Finset.single_le_sum
      (f := fun i' : Fin n => ∑ j' : Fin n, ∑ k' : Fin n, ∑ l' : Fin n, X i' j' k' l' ^ 2)
      (fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun c _ =>
        Finset.sum_nonneg fun d _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

lemma abs_apply_le_sqrt_frobSq (X : Curv4 n) (i j k l : Fin n) :
    |X i j k l| ≤ Real.sqrt (frobSq X) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_apply_le_frobSq X i j k l)

lemma sqrt_frobSq_mul_self (X : Curv4 n) :
    Real.sqrt (frobSq X) * Real.sqrt (frobSq X) = frobSq X := by
  rw [← sq]
  exact Real.sq_sqrt (frobSq_nonneg X)

/-! ## Constant sums over `Fin n` -/

lemma sum2_add (f g : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, (f p q + g p q)) = (∑ p, ∑ q, f p q) + ∑ p, ∑ q, g p q := by
  simp only [Finset.sum_add_distrib]

lemma sum2_sub (f g : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, (f p q - g p q)) = (∑ p, ∑ q, f p q) - ∑ p, ∑ q, g p q := by
  simp only [Finset.sum_sub_distrib]

lemma sum2_const_mul (c : ℝ) (f : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, c * f p q) = c * ∑ p, ∑ q, f p q := by
  simp only [← Finset.mul_sum]

lemma sum2_const (c : ℝ) : (∑ _p : Fin n, ∑ _q : Fin n, c) = (n : ℝ) ^ 2 * c := by
  have h : (∑ _p : Fin n, ∑ _q : Fin n, c) = (n : ℝ) * ((n : ℝ) * c) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [h]; ring

lemma sum4_const (c : ℝ) :
    (∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n, ∑ _l : Fin n, c) = (n : ℝ) ^ 4 * c := by
  have h : (∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n, ∑ _l : Fin n, c) =
      (n : ℝ) * ((n : ℝ) * ((n : ℝ) * ((n : ℝ) * c))) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [h]; ring

/-! ## A componentwise bound upgrades to a `frobSq` bound -/

lemma frobSq_le_of_comp_bound (X : Curv4 n) (M : ℝ)
    (h : ∀ i j k l, |X i j k l| ≤ M) : frobSq X ≤ (n : ℝ) ^ 4 * M ^ 2 := by
  have hle : frobSq X ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n, ∑ _l : Fin n, M ^ 2 := by
    simp only [frobSq]
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    apply Finset.sum_le_sum; intro k _
    apply Finset.sum_le_sum; intro l _
    exact sq_le_sq' (abs_le.mp (h i j k l)).1 (abs_le.mp (h i j k l)).2
  rwa [sum4_const] at hle

end Work.Diff.Alg.PA
