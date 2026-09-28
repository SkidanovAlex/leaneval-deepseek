import Mathlib

namespace Work.HP.MDEstimates

open scoped BigOperators

/-- Counting bound for the `n = 3` case: the sum of `2 ^ (min k s - k)` over
`k ∈ range (M + 1)` is at most `s + 2`.  The first `s + 1` terms equal `1` and
the remaining terms form a geometric series of ratio `1/2`, whose total is at
most `1`. -/
lemma geom_min_k_sum_count (M s : ℕ) :
    (∑ k ∈ Finset.range (M+1), (2:ℝ) ^ ((min k s : ℝ) - (k:ℝ))) ≤ (s:ℝ) + 2 := by
  let d : ℕ → ℝ := fun k => (2:ℝ) ^ ((min k s : ℝ) - (k:ℝ))
  change (∑ k ∈ Finset.range (M+1), d k) ≤ (s:ℝ) + 2
  by_cases hMs : M ≤ s
  · have hterm : ∀ k ∈ Finset.range (M+1), d k = 1 := by
      intro k hk
      have hkM : (k:ℝ) ≤ (s:ℝ) := by
        exact_mod_cast (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hMs)
      simp only [d]
      rw [min_eq_left hkM]
      simp
    rw [Finset.sum_congr rfl hterm]
    have hone : (∑ _x ∈ Finset.range (M+1), (1:ℝ)) = (M:ℝ)+1 := by simp
    rw [hone]
    have : (M:ℝ) ≤ (s:ℝ) := by exact_mod_cast hMs
    linarith
  · have hdecomp : M + 1 = (s+1) + (M - s) := by omega
    rw [hdecomp, Finset.sum_range_add d]
    have hfirst : (∑ i ∈ Finset.range (s+1), d i) = (s:ℝ) + 1 := by
      have hterm : ∀ i ∈ Finset.range (s+1), d i = 1 := by
        intro i hi
        have his : (i:ℝ) ≤ (s:ℝ) := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        simp only [d]
        rw [min_eq_left his]; simp
      rw [Finset.sum_congr rfl hterm]
      simp
    have hsecond : (∑ j ∈ Finset.range (M - s), d ((s+1)+j)) ≤ 1 := by
      have hterm : ∀ j : ℕ, d ((s+1)+j) = ((1/2:ℝ))^(j+1) := by
        intro j
        have hle : (s:ℝ) ≤ ((s+1+j:ℕ):ℝ) := by
          have : s ≤ s+1+j := by omega
          exact_mod_cast this
        simp only [d]
        rw [min_eq_right hle]
        rw [show (s:ℝ) - ((s+1+j:ℕ):ℝ) = -((j+1:ℕ):ℝ) by push_cast; ring]
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
        rw [Real.rpow_natCast]
        rw [← inv_pow]
        norm_num
      rw [Finset.sum_congr rfl (fun j _ => hterm j)]
      have hsum : (∑ j ∈ Finset.range (M - s), (1/2:ℝ)^(j+1))
          = (1/2) * (∑ j ∈ Finset.range (M - s), (1/2:ℝ)^j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_succ]
        ring
      rw [hsum]
      have hgeom := geom_sum_eq (show (1/2:ℝ) ≠ 1 by norm_num) (M - s)
      rw [hgeom]
      have hmain : (1/2) * (((1/2:ℝ)^(M-s) - 1) / ((1/2) - 1)) = 1 - (1/2)^(M-s) := by
        field_simp
        ring
      rw [hmain]
      have hpos : (0:ℝ) ≤ (1/2)^(M-s) := by positivity
      linarith
    rw [hfirst]
    linarith

theorem geom_min_k_sum (n M s : ℕ) (hn : 3 ≤ n) :
    (∑ k ∈ Finset.range (M+1), (2:ℝ)^(((n:ℝ)-2)*(min k s : ℝ) - (k:ℝ)))
      ≤ ((s:ℝ)+2) * (2:ℝ)^(((n:ℝ)-3)*(s:ℝ)) := by
  have hstep : ∀ k, (2:ℝ)^(((n:ℝ)-2)*(min k s : ℝ) - (k:ℝ))
      ≤ (2:ℝ)^(((n:ℝ)-3)*(s:ℝ)) * (2:ℝ)^((min k s : ℝ) - (k:ℝ)) := by
    intro k
    have hExp : ((n:ℝ)-2)*(min k s : ℝ) - (k:ℝ)
        ≤ ((n:ℝ)-3)*(s:ℝ) + ((min k s : ℝ) - (k:ℝ)) := by
      have h1 : (min k s : ℝ) ≤ (s:ℝ) := min_le_right _ _
      have h3 : (0:ℝ) ≤ (n:ℝ) - 3 := by
        have : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        linarith
      have hmul : ((n:ℝ)-3) * (min k s : ℝ) ≤ ((n:ℝ)-3) * (s:ℝ) :=
        mul_le_mul_of_nonneg_left h1 h3
      nlinarith [hmul]
    have hmono := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) hExp
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)] at hmono
    exact hmono
  calc
    (∑ k ∈ Finset.range (M+1), (2:ℝ)^(((n:ℝ)-2)*(min k s : ℝ) - (k:ℝ)))
      ≤ ∑ k ∈ Finset.range (M+1), (2:ℝ)^(((n:ℝ)-3)*(s:ℝ)) * (2:ℝ)^((min k s : ℝ) - (k:ℝ)) :=
        Finset.sum_le_sum (fun k _ => hstep k)
    _ = (2:ℝ)^(((n:ℝ)-3)*(s:ℝ)) * ∑ k ∈ Finset.range (M+1), (2:ℝ)^((min k s : ℝ) - (k:ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (2:ℝ)^(((n:ℝ)-3)*(s:ℝ)) * ((s:ℝ)+2) :=
        mul_le_mul_of_nonneg_left (geom_min_k_sum_count M s) (Real.rpow_nonneg (by norm_num) _)
    _ = ((s:ℝ) + 2) * (2:ℝ)^(((n:ℝ)-3)*(s:ℝ)) := by ring

end Work.HP.MDEstimates
