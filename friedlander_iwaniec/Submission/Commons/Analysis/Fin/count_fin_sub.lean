import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval

namespace Commons.Analysis.Fin

open scoped BigOperators
open Finset

private def coef (K : ℕ) (k : ℤ) : ℂ := (((K : ℝ) - |(k : ℝ)| : ℝ) : ℂ)

private lemma coef_succ (K : ℕ) (k : ℤ) : coef (K+1) k = coef K k + 1 := by
  simp only [coef]
  push_cast
  ring

private lemma coef_neg_self (K : ℕ) : coef K (-(K:ℤ)) = 0 := by
  simp only [coef]
  push_cast
  rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg K)]
  simp

private lemma coef_self (K : ℕ) : coef K ((K:ℤ)) = 0 := by
  simp only [coef]
  push_cast
  rw [abs_of_nonneg (Nat.cast_nonneg K)]
  simp

/-- Rewrite a sum over an integer interval `[a,b]` as a sum over `range`. -/
private lemma sum_Icc_eq_sum_range_int (a b : ℤ) (g : ℤ → ℂ) :
    ∑ k ∈ Finset.Icc a b, g k = ∑ j ∈ Finset.range (b + 1 - a).toNat, g (a + (j:ℤ)) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]

/-- Splitting `range (2K+1)` into the two end blocks. -/
private lemma sum_range_decomp (K : ℕ) (g : ℤ → ℂ) :
    ∑ j ∈ Finset.range (2*K+1), g ((j:ℤ) - (K:ℤ))
      = ∑ n ∈ Finset.range K, g ((n:ℤ) - (K:ℤ)) + g 0 + ∑ n ∈ Finset.range K, g ((n:ℤ) + 1) := by
  have h1 : (2*K+1 : ℕ) = K + (K+1) := by ring
  rw [h1, Finset.sum_range_add]
  have h2 : ∀ x : ℕ, g (((K+x : ℕ):ℤ) - (K:ℤ)) = g ((x:ℤ)) := by
    intro x; congr 1; push_cast; ring
  rw [Finset.sum_congr rfl (fun x _ => h2 x)]
  have h4 : ∑ x ∈ Finset.range (K+1), g ((x:ℤ)) = g 0 + ∑ x ∈ Finset.range K, g ((x:ℤ) + 1) := by
    rw [show (K+1:ℕ) = 1 + K from by ring, Finset.sum_range_add, Finset.sum_range_one]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    push_cast; ring
  rw [h4]
  abel

/-- Dropping the two end points `±(K+1)` from `Icc (-(K+1)) (K+1)`, where the
coefficient `K+1-|k|` vanishes. -/
private lemma B2_succ (K : ℕ) (f : ℤ → ℂ) :
    (∑ k ∈ Finset.Icc (-((K+1:ℕ):ℤ)) ((K+1:ℕ):ℤ), coef (K+1) k * f k)
      = (∑ k ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), coef K k * f k)
        + ∑ k ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), f k := by
  have hdrop : (∑ k ∈ Finset.Icc (-((K+1:ℕ):ℤ)) ((K+1:ℕ):ℤ), coef (K+1) k * f k)
      = ∑ k ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), coef (K+1) k * f k :=
    (Finset.sum_subset
      (s₁ := Finset.Icc (-(K:ℤ)) (K:ℤ))
      (s₂ := Finset.Icc (-((K+1:ℕ):ℤ)) ((K+1:ℕ):ℤ))
      (by intro x hx; simp only [Finset.mem_Icc] at hx ⊢; constructor <;> omega)
      (by
        intro x hx hxn
        simp only [Finset.mem_Icc] at hx hxn
        have hx' : x = -((K+1:ℕ):ℤ) ∨ x = ((K+1:ℕ):ℤ) := by omega
        rcases hx' with h | h
        · subst h; rw [coef_neg_self (K+1)]; ring
        · subst h; rw [coef_self (K+1)]; ring)).symm
  rw [hdrop, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [coef_succ]
  ring

/-- The sum over `Icc (-K) K` with the `K-|k|` coefficient may be restricted to
`Icc (-(K-1)) (K-1)`, since the coefficients at `±K` vanish. -/
private lemma B2_eq (K : ℕ) (f : ℤ → ℂ) :
    (∑ k ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), coef K k * f k)
      = ∑ k ∈ Finset.Icc (-((K:ℤ)-1)) ((K:ℤ)-1), coef K k * f k := by
  refine (Finset.sum_subset
    (s₁ := Finset.Icc (-((K:ℤ)-1)) ((K:ℤ)-1))
    (s₂ := Finset.Icc (-(K:ℤ)) (K:ℤ)) ?_ ?_).symm
  · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · intro x hx hxn
    simp only [Finset.mem_Icc] at hx hxn
    have hx' : x = -(K:ℤ) ∨ x = ((K:ℤ)) := by omega
    rcases hx' with h | h
    · subst h; rw [coef_neg_self K]; ring
    · subst h; rw [coef_self K]; ring

/-- Main induction: the double sum equals the single `Icc (-K) K` sum. -/
private lemma main_ind (f : ℤ → ℂ) (K : ℕ) :
    (∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, f ((m:ℤ) - (n:ℤ)))
      = ∑ k ∈ Finset.Icc (-(K:ℤ)) (K:ℤ), coef K k * f k := by
  induction K with
  | zero => simp [coef]
  | succ K ih =>
    rw [Finset.sum_range_succ]
    simp only [Finset.sum_range_succ]
    rw [Finset.sum_add_distrib, ih]
    have hrefl : ∑ n ∈ Finset.range K, f ((K:ℤ) - (n:ℤ))
        = ∑ n ∈ Finset.range K, f ((n:ℤ) + 1) := by
      conv_lhs => rw [← Finset.sum_range_reflect (fun n : ℕ => f ((K:ℤ) - (n:ℤ))) K]
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      simp only [Finset.mem_range] at hj
      omega
    rw [hrefl]
    have h0 : (K:ℤ) - (K:ℤ) = (0:ℤ) := by ring
    rw [h0]
    rw [B2_succ K f]
    rw [sum_Icc_eq_sum_range_int (-(K:ℤ)) (K:ℤ) f]
    have hIdx : ((K:ℤ) + 1 - (-(K:ℤ))).toNat = 2*K+1 := by
      have : (K:ℤ) + 1 - (-(K:ℤ)) = ((2*K+1 : ℕ):ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]
    rw [hIdx]
    have hsum2 : (∑ j ∈ Finset.range (2*K+1), f (-(K:ℤ) + (j:ℤ)))
        = ∑ j ∈ Finset.range (2*K+1), f ((j:ℤ) - (K:ℤ)) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      ring
    rw [hsum2, sum_range_decomp K f]
    abel

theorem count_fin_sub (K : ℕ) (f : ℤ → ℂ) :
    (∑ m : Fin K, ∑ n : Fin K, f ((m.val : ℤ) - (n.val : ℤ)))
      = ∑ k ∈ Finset.Icc (-((K:ℤ)-1)) ((K:ℤ)-1),
          ((((K:ℝ) - |((k:ℝ))|) : ℝ) : ℂ) * f k := by
  rw [show (∑ m : Fin K, ∑ n : Fin K, f ((m.val : ℤ) - (n.val : ℤ)))
      = ∑ m ∈ Finset.range K, ∑ n ∈ Finset.range K, f ((m:ℤ) - (n:ℤ)) from by
    rw [Fin.sum_univ_eq_sum_range (fun mv : ℕ => ∑ n : Fin K, f ((mv:ℤ) - (n.val:ℤ))) K]
    apply Finset.sum_congr rfl
    intro m _
    rw [Fin.sum_univ_eq_sum_range (fun nv : ℕ => f ((m:ℤ) - (nv:ℤ))) K]]
  rw [main_ind f K]
  exact B2_eq K f

end Commons.Analysis.Fin