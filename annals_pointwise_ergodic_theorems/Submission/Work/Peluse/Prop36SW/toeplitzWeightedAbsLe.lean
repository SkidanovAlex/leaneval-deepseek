import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.Prop36SW

open Finset

/-- For `a b n : ℕ`, the square of the difference of the two step indicators
`1_{a ≤ n}`, `1_{b ≤ n}` is the indicator of the "cut at `n` separating `a` and `b`". -/
private lemma ind_pointwise (a b n : ℕ) :
    ((if a ≤ n then (1:ℝ) else 0) - (if b ≤ n then (1:ℝ) else 0))^2
      = (if (min a b ≤ n ∧ n < max a b) then (1:ℝ) else 0) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab]
    by_cases ha : a ≤ n
    · by_cases hb : b ≤ n
      · rw [if_pos ha, if_pos hb, sub_self, zero_pow (by norm_num), if_neg (by omega)]
      · rw [if_pos ha, if_neg hb, sub_zero, one_pow, if_pos (by omega)]
    · rw [if_neg ha, if_neg (fun hb => ha (le_trans hab hb)), sub_self,
        zero_pow (by norm_num), if_neg (by omega)]
  · rw [min_eq_right hab, max_eq_left hab]
    by_cases hb : b ≤ n
    · by_cases ha : a ≤ n
      · rw [if_pos ha, if_pos hb, sub_self, zero_pow (by norm_num), if_neg (by omega)]
      · rw [if_neg ha, if_pos hb, zero_sub, neg_sq, one_pow, if_pos (by omega)]
    · rw [if_neg (fun ha => hb (le_trans hab ha)), if_neg hb, sub_self,
        zero_pow (by norm_num), if_neg (by omega)]

/-- Count of the cuts `n ∈ [0,M)` that separate `a` and `b` (both `≤ M`), equal to `|a-b|`. -/
private lemma cutSum (M a b : ℕ) (ha : a ≤ M) (hb : b ≤ M) :
    (∑ n ∈ Finset.range M, ((if a ≤ n then (1:ℝ) else 0) - (if b ≤ n then (1:ℝ) else 0))^2)
      = ((max a b - min a b : ℕ) : ℝ) := by
  rw [Finset.sum_congr rfl (fun n _ => ind_pointwise a b n), Finset.sum_boole]
  rw [show (Finset.range M).filter (fun n => min a b ≤ n ∧ n < max a b)
        = Finset.Ico (min a b) (max a b) from by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by have := max_le ha hb; omega, h1, h2⟩]
  simp

/-- `|j-k|` (as a real) equals `max - min` of the underlying naturals. -/
private lemma absEq (W : ℕ) (j k : Fin W) :
    (|((j:ℤ)-(k:ℤ))| : ℝ) = ((max (j:ℕ) (k:ℕ) - min (j:ℕ) (k:ℕ) : ℕ) : ℝ) := by
  push_cast
  rw [Nat.cast_sub (min_le_max), Nat.cast_max, Nat.cast_min]
  rw [eq_comm, max_sub_min_eq_abs, abs_sub_comm]

/-- Pointwise cut decomposition of `|j-k|`. -/
private lemma absEqCutSum (W : ℕ) (hW : 1 ≤ W) (j k : Fin W) :
    (|((j:ℤ)-(k:ℤ))| : ℝ)
      = ∑ n ∈ Finset.range (W-1),
          ((if (j:ℕ) ≤ n then (1:ℝ) else 0) - (if (k:ℕ) ≤ n then (1:ℝ) else 0))^2 := by
  rw [absEq, ← cutSum (W-1) (j:ℕ) (k:ℕ) (by omega) (by omega)]

/-- Splitting a sum of `A + B - 2 C` into the three sums. -/
private lemma sum_split {ι : Type*} (s : Finset ι) (A B C : ι → ℝ) :
    ∑ i ∈ s, (A i + B i - 2 * C i) = ∑ i ∈ s, A i + ∑ i ∈ s, B i - 2 * ∑ i ∈ s, C i := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- Symmetry of `Re (z * conj w)` in its two arguments. -/
private lemma swapRe (z w : ℂ) : (w * star z).re = (z * star w).re := by
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The inner sum at cut `n` evaluates to `2 * Re (P_n * conj (S - P_n))`. -/
private lemma cutoff_inner (W : ℕ) (c : Fin W → ℂ) (n : ℕ) :
    (∑ j : Fin W, ∑ k : Fin W,
      ((if (j:ℕ) ≤ n then (1:ℝ) else 0) - (if (k:ℕ) ≤ n then (1:ℝ) else 0))^2
        * (c j * star (c k)).re)
    = 2 * ((∑ j : Fin W, if (j:ℕ) ≤ n then c j else 0)
            * star ((∑ j : Fin W, c j) - ∑ j : Fin W, if (j:ℕ) ≤ n then c j else 0)).re := by
  have hA : (∑ j : Fin W, ∑ k : Fin W, ((if (j:ℕ) ≤ n then c j else 0) * star (c k)).re)
      = ((∑ j : Fin W, if (j:ℕ) ≤ n then c j else 0) * star (∑ j : Fin W, c j)).re := by
    simp only [← Complex.re_sum]
    congr 1
    rw [show (∑ i : Fin W, ∑ k : Fin W, (if (i:ℕ) ≤ n then c i else 0) * star (c k))
          = ∑ i : Fin W, (if (i:ℕ) ≤ n then c i else 0) * (∑ k : Fin W, star (c k)) from by
        apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]]
    rw [show (∑ i : Fin W, (if (i:ℕ) ≤ n then c i else 0) * (∑ k : Fin W, star (c k)))
          = (∑ i : Fin W, (if (i:ℕ) ≤ n then c i else 0)) * (∑ k : Fin W, star (c k)) from
        (Finset.sum_mul _ _ _).symm]
    rw [star_sum]
  have hB : (∑ j : Fin W, ∑ k : Fin W, (c j * star (if (k:ℕ) ≤ n then c k else 0)).re)
      = ((∑ j : Fin W, if (j:ℕ) ≤ n then c j else 0) * star (∑ j : Fin W, c j)).re := by
    rw [show (∑ j : Fin W, ∑ k : Fin W, (c j * star (if (k:ℕ) ≤ n then c k else 0)).re)
          = ((∑ j : Fin W, c j) * star (∑ k : Fin W, if (k:ℕ) ≤ n then c k else 0)).re from by
        rw [Finset.sum_comm]
        simp only [← Complex.re_sum]
        congr 1
        rw [show (∑ k : Fin W, ∑ j : Fin W, c j * star (if (k:ℕ) ≤ n then c k else 0))
              = ∑ k : Fin W, (∑ j : Fin W, c j) * star (if (k:ℕ) ≤ n then c k else 0) from by
            apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_mul]]
        rw [show (∑ k : Fin W, (∑ j : Fin W, c j) * star (if (k:ℕ) ≤ n then c k else 0))
              = (∑ j : Fin W, c j) * (∑ k : Fin W, star (if (k:ℕ) ≤ n then c k else 0)) from
            (Finset.mul_sum _ _ _).symm]
        rw [star_sum]]
    rw [swapRe (∑ j : Fin W, if (j:ℕ) ≤ n then c j else 0) (∑ j : Fin W, c j)]
  have hC : (∑ j : Fin W, ∑ k : Fin W,
        ((if (j:ℕ) ≤ n then c j else 0) * star (if (k:ℕ) ≤ n then c k else 0)).re)
      = ((∑ j : Fin W, if (j:ℕ) ≤ n then c j else 0)
          * star (∑ j : Fin W, if (j:ℕ) ≤ n then c j else 0)).re := by
    simp only [← Complex.re_sum]
    congr 1
    rw [show (∑ i : Fin W, ∑ k : Fin W,
              (if (i:ℕ) ≤ n then c i else 0) * star (if (k:ℕ) ≤ n then c k else 0))
          = ∑ i : Fin W, (if (i:ℕ) ≤ n then c i else 0)
              * (∑ k : Fin W, star (if (k:ℕ) ≤ n then c k else 0)) from by
        apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]]
    rw [show (∑ i : Fin W, (if (i:ℕ) ≤ n then c i else 0)
              * (∑ k : Fin W, star (if (k:ℕ) ≤ n then c k else 0)))
          = (∑ i : Fin W, (if (i:ℕ) ≤ n then c i else 0))
              * (∑ k : Fin W, star (if (k:ℕ) ≤ n then c k else 0)) from
        (Finset.sum_mul _ _ _).symm]
    rw [star_sum]
  have hpt : ∀ j k : Fin W,
      ((if (j:ℕ) ≤ n then (1:ℝ) else 0) - (if (k:ℕ) ≤ n then (1:ℝ) else 0))^2
          * (c j * star (c k)).re
      = ((if (j:ℕ) ≤ n then c j else 0) * star (c k)).re
        + (c j * star (if (k:ℕ) ≤ n then c k else 0)).re
        - 2 * ((if (j:ℕ) ≤ n then c j else 0) * star (if (k:ℕ) ≤ n then c k else 0)).re := by
    intro j k
    by_cases hj : (j:ℕ) ≤ n <;> by_cases hk : (k:ℕ) ≤ n <;> simp [hj, hk] <;> ring
  rw [Finset.sum_congr rfl (fun (j : Fin W) _ => Finset.sum_congr rfl (fun (k : Fin W) _ => hpt j k))]
  rw [Finset.sum_congr rfl (fun (j : Fin W) _ => sum_split (Finset.univ : Finset (Fin W))
        (fun (k : Fin W) => ((if (j:ℕ) ≤ n then c j else 0) * star (c k)).re)
        (fun (k : Fin W) => (c j * star (if (k:ℕ) ≤ n then c k else 0)).re)
        (fun (k : Fin W) =>
          ((if (j:ℕ) ≤ n then c j else 0) * star (if (k:ℕ) ≤ n then c k else 0)).re))]
  rw [sum_split (Finset.univ : Finset (Fin W))
        (fun (j : Fin W) => ∑ k : Fin W, ((if (j:ℕ) ≤ n then c j else 0) * star (c k)).re)
        (fun (j : Fin W) => ∑ k : Fin W, (c j * star (if (k:ℕ) ≤ n then c k else 0)).re)
        (fun (j : Fin W) => ∑ k : Fin W,
            ((if (j:ℕ) ≤ n then c j else 0) * star (if (k:ℕ) ≤ n then c k else 0)).re)]
  rw [hA, hB, hC]
  rw [← two_mul, ← mul_sub, ← Complex.sub_re, star_sub, mul_sub]

/-- Quadratic bound used for each cut. -/
private lemma quadBound (S P : ℂ) : 4 * (P * star (S - P)).re ≤ ‖S‖ ^ 2 := by
  have h := Complex.normSq_add P (S - P)
  rw [add_sub_cancel] at h
  have hnorm : ‖S‖ ≤ ‖P‖ + ‖S - P‖ := by
    have := norm_add_le P (S - P); rwa [add_sub_cancel] at this
  have hkey : ‖S‖^2 ≤ 2*‖P‖^2 + 2*‖S-P‖^2 := by
    nlinarith [hnorm, norm_nonneg S, norm_nonneg P, norm_nonneg (S - P),
      sq_nonneg (‖P‖ - ‖S - P‖)]
  simp only [Complex.normSq_eq_norm_sq] at h
  simp only [Complex.star_def]
  nlinarith [h, hkey]

theorem toeplitzWeightedAbsLe (W : ℕ) (hW : 1 ≤ W) (c : Fin W → ℂ) :
    2 * (∑ j : Fin W, ∑ k : Fin W, (|((j : ℤ) - (k : ℤ))| : ℝ) * (c j * star (c k)).re)
      ≤ ((W : ℝ) - 1) * ‖∑ j : Fin W, c j‖ ^ 2 := by
  have hstep1 : (∑ j : Fin W, ∑ k : Fin W, (|((j : ℤ) - (k : ℤ))| : ℝ) * (c j * star (c k)).re)
      = ∑ n ∈ Finset.range (W-1), ∑ j : Fin W, ∑ k : Fin W,
          ((if (j:ℕ) ≤ n then (1:ℝ) else 0) - (if (k:ℕ) ≤ n then (1:ℝ) else 0))^2
            * (c j * star (c k)).re := by
    rw [show (∑ j : Fin W, ∑ k : Fin W, (|((j : ℤ) - (k : ℤ))| : ℝ) * (c j * star (c k)).re)
          = ∑ j : Fin W, ∑ k : Fin W,
              (∑ n ∈ Finset.range (W-1),
                ((if (j:ℕ) ≤ n then (1:ℝ) else 0) - (if (k:ℕ) ≤ n then (1:ℝ) else 0))^2)
                * (c j * star (c k)).re from by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        rw [absEqCutSum W hW j k]]
    simp only [Finset.sum_mul]
    rw [show (∑ j : Fin W, ∑ k : Fin W, ∑ n ∈ Finset.range (W-1),
                ((if (j:ℕ) ≤ n then (1:ℝ) else 0) - (if (k:ℕ) ≤ n then (1:ℝ) else 0))^2
                  * (c j * star (c k)).re)
          = ∑ n ∈ Finset.range (W-1), ∑ j : Fin W, ∑ k : Fin W,
              ((if (j:ℕ) ≤ n then (1:ℝ) else 0) - (if (k:ℕ) ≤ n then (1:ℝ) else 0))^2
                * (c j * star (c k)).re from by
        rw [show (∑ j : Fin W, ∑ k : Fin W, ∑ n ∈ Finset.range (W-1),
                    ((if (j:ℕ) ≤ n then (1:ℝ) else 0) - (if (k:ℕ) ≤ n then (1:ℝ) else 0))^2
                      * (c j * star (c k)).re)
              = ∑ j : Fin W, ∑ n ∈ Finset.range (W-1), ∑ k : Fin W,
                  ((if (j:ℕ) ≤ n then (1:ℝ) else 0) - (if (k:ℕ) ≤ n then (1:ℝ) else 0))^2
                    * (c j * star (c k)).re from by
            apply Finset.sum_congr rfl; intro j _; exact Finset.sum_comm]
        exact Finset.sum_comm]
  rw [hstep1, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun n _ => by rw [cutoff_inner W c n])]
  refine le_trans (b := ∑ n ∈ Finset.range (W-1), ‖∑ j : Fin W, c j‖ ^ 2)
    (Finset.sum_le_sum (fun n _ => ?_)) ?_
  · have h := quadBound (∑ j : Fin W, c j) (∑ j : Fin W, if (j:ℕ) ≤ n then c j else 0)
    nlinarith [h]
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub hW]
    norm_num

end Work.Peluse.Prop36SW
