import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-!
# A tail bound for the `p`-series on `ℤ`

For `j ≥ 2` and `K ≥ 1`,
`∑' k : ℤ, [K ≤ |k|] / |k|^j ≤ C * K ^ (1 - j)`.

The proof reduces the sum over `ℤ` to twice a sum over `ℕ` (the summand is even),
shifts the sum by `⌈K⌉₊`, and bounds the resulting `p`-series tail by an integral.
-/

open Set MeasureTheory intervalIntegral Filter

namespace Commons.Analysis.PSeries

/-- Summability of the shifted `p`-series. -/
private lemma summable_nat_rpow_neg_shift (s : ℝ) (hs : 1 < s) (m : ℕ) :
    Summable (fun n : ℕ => (((n + m : ℕ) : ℝ) ^ (-s))) :=
  (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-s)) m).mpr
    (Real.summable_nat_rpow.mpr (by linarith))

/-- Tail bound for the `p`-series on `ℕ`: for `2 ≤ s` the tail `∑_{n ≥ m} n ^ (-s)`
is at most `2 * m ^ (1 - s)`. -/
private lemma tsum_nat_rpow_neg_shift_tail {s : ℝ} (hs : 2 ≤ s) {m : ℕ} (hm : 1 ≤ m) :
    (∑' n : ℕ, (((n + m : ℕ) : ℝ) ^ (-s))) ≤ 2 * (m : ℝ) ^ (1 - s) := by
  have hs1 : 1 < s := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
  have hsumm := summable_nat_rpow_neg_shift s hs1 m
  -- split off the first term
  have hsplit : (∑' n : ℕ, (((n + m : ℕ) : ℝ) ^ (-s)))
      = (m : ℝ) ^ (-s) + ∑' n : ℕ, (((n + m + 1 : ℕ) : ℝ) ^ (-s)) := by
    rw [Summable.tsum_eq_zero_add hsumm]
    rw [tsum_congr (fun n : ℕ => by
      rw [show (n + 1) + m = n + m + 1 by omega])]
    simp
  -- integral test
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Ici (m : ℝ)) := by
    intro x hx y _ hxy
    simp only [mem_Ici] at hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
  have hnonneg : ∀ t ∈ Ioi (m : ℝ), 0 ≤ t ^ (-s) := by
    intro t ht
    simp only [mem_Ioi] at ht
    exact Real.rpow_nonneg (le_of_lt (by linarith)) _
  have hint : IntegrableOn (fun x : ℝ => x ^ (-s)) (Ioi (m : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (a := -s) (c := (m : ℝ)) (by linarith) hmpos
  have hW : (∑' n : ℕ, (((n + m + 1 : ℕ) : ℝ) ^ (-s))) ≤ ∫ x in Ioi (m : ℝ), x ^ (-s) :=
    AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-s)) m hanti hint hnonneg
  have hintval : ∫ x in Ioi (m : ℝ), x ^ (-s) = (m : ℝ) ^ (1 - s) / (s - 1) := by
    rw [integral_Ioi_rpow_of_lt (a := -s) (c := (m : ℝ)) (by linarith) hmpos]
    rw [show (-s + 1 : ℝ) = 1 - s by ring]
    rw [show (1 - s : ℝ) = -(s - 1) by ring, div_neg]
    ring
  have hIntle : ∫ x in Ioi (m : ℝ), x ^ (-s) ≤ (m : ℝ) ^ (1 - s) := by
    rw [hintval]
    exact div_le_self (Real.rpow_nonneg (le_of_lt hmpos) _) (by linarith)
  have hfirst : (m : ℝ) ^ (-s) ≤ (m : ℝ) ^ (1 - s) := by
    have hpow := Real.rpow_add hmpos (-s) 1
    rw [Real.rpow_one] at hpow
    rw [show -s + 1 = 1 - s by ring] at hpow
    calc (m : ℝ) ^ (-s) = (m : ℝ) ^ (-s) * 1 := (mul_one _).symm
      _ ≤ (m : ℝ) ^ (-s) * (m : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hm) (Real.rpow_nonneg (le_of_lt hmpos) _)
      _ = (m : ℝ) ^ (1 - s) := hpow.symm
  calc (∑' n : ℕ, (((n + m : ℕ) : ℝ) ^ (-s)))
      = (m : ℝ) ^ (-s) + ∑' n : ℕ, (((n + m + 1 : ℕ) : ℝ) ^ (-s)) := hsplit
    _ ≤ (m : ℝ) ^ (1 - s) + (m : ℝ) ^ (1 - s) := add_le_add hfirst (hW.trans hIntle)
    _ = 2 * (m : ℝ) ^ (1 - s) := by ring

theorem tsum_int_abs_pow_neg_tail_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (K : ℝ), 2 ≤ j → 1 ≤ K →
      (∑' k : ℤ, (if K ≤ |(k : ℝ)| then ((|(k : ℝ)|) ^ j)⁻¹ else 0))
        ≤ C * K ^ (1 - (j : ℝ)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro j K hj hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  -- the ceiling `m` of `K`
  set m : ℕ := Nat.ceil K with hmdef
  have hmpos : 0 < m := by rw [hmdef]; exact Nat.lt_ceil.mpr (by simpa using hKpos)
  have hm1 : 1 ≤ m := hmpos
  have hmK : K ≤ (m : ℝ) := by rw [hmdef]; exact Nat.le_ceil K
  have hm_lt : (m : ℝ) - 1 < K := by
    have h := Nat.ceil_lt_add_one (a := K) (show (0 : ℝ) ≤ K by linarith)
    rw [← hmdef] at h
    linarith
  -- the summand
  set f : ℤ → ℝ := fun k => if K ≤ |(k : ℝ)| then ((|(k : ℝ)|) ^ j)⁻¹ else 0 with hfdef
  change (∑' k : ℤ, f k) ≤ 4 * K ^ (1 - (j : ℝ))
  have hf_even : ∀ k : ℤ, f (-k) = f k := by
    intro k
    simp only [hfdef, Int.cast_neg, abs_neg]
  -- summability of the two halfline sums
  have hS : Summable (fun n : ℕ => (n : ℝ) ^ (-(j : ℝ))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have h1 : Summable (fun n : ℕ => f (n : ℤ)) := by
    refine Summable.of_nonneg_of_le (g := fun n : ℕ => f (n : ℤ))
      (f := fun n : ℕ => (n : ℝ) ^ (-(j : ℝ))) ?_ ?_ hS
    · intro n
      simp only [hfdef, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
      split_ifs
      · exact inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg n) j)
      · exact le_refl 0
    · intro n
      simp only [hfdef, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
      split_ifs with h
      · rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast]
      · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h2 : Summable (fun n : ℕ => f (-(n : ℤ))) :=
    h1.congr (fun n => (hf_even (n : ℤ)).symm)
  have hZval : (∑' k : ℤ, f k) = 2 * (∑' n : ℕ, f (n : ℤ)) := by
    have hval := Summable.tsum_of_nat_of_neg h1 h2
    have hneg : (∑' n : ℕ, f (-(n : ℤ))) = ∑' n : ℕ, f (n : ℤ) :=
      tsum_congr (fun n => hf_even (n : ℤ))
    have hf0 : f 0 = 0 := by
      have hnot : ¬ (K ≤ |((0 : ℤ) : ℝ)|) := by
        simpa only [Int.cast_zero, abs_zero] using not_le.mpr (by linarith : (0 : ℝ) < K)
      simp only [hfdef]
      rw [if_neg hnot]
    rw [hval, hneg, hf0]
    ring
  -- the halfline sum
  have hT : (∑' n : ℕ, f (n : ℤ)) ≤ 2 * K ^ (1 - (j : ℝ)) := by
    have hshift : (∑' n : ℕ, f (n : ℤ)) = ∑' n : ℕ, f ((n + m : ℕ) : ℤ) := by
      have hzero : (∑ i ∈ Finset.range m, f (i : ℤ)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        have hiK : (i : ℝ) < K := by
          rw [hmdef] at hi
          exact Nat.lt_ceil.mp hi
        have hnot : ¬ (K ≤ |((i : ℤ) : ℝ)|) := by
          have habs : |((i : ℤ) : ℝ)| = (i : ℝ) := by
            rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg i : (0 : ℝ) ≤ (i : ℝ))]
          rw [habs]
          exact not_le.mpr hiK
        simp only [hfdef]
        rw [if_neg hnot]
      have h := Summable.sum_add_tsum_nat_add m h1
      rw [hzero, zero_add] at h
      exact h.symm
    rw [hshift]
    have hterm : (∑' n : ℕ, f ((n + m : ℕ) : ℤ))
        = ∑' n : ℕ, (((n + m : ℕ) : ℝ) ^ (-(j : ℝ))) := by
      apply tsum_congr
      intro n
      have hnn : (0 : ℝ) ≤ ((n + m : ℕ) : ℝ) := Nat.cast_nonneg _
      have hKle : K ≤ ((n + m : ℕ) : ℝ) :=
        le_trans hmK (by exact_mod_cast (Nat.le_add_left m n))
      simp only [hfdef, Int.cast_natCast, abs_of_nonneg hnn, if_pos hKle]
      rw [Real.rpow_neg hnn, Real.rpow_natCast]
    rw [hterm]
    refine (tsum_nat_rpow_neg_shift_tail hjR hm1).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hKpos hmK (by linarith : (1 : ℝ) - (j : ℝ) ≤ 0))
      (by norm_num)
  calc (∑' k : ℤ, f k) = 2 * (∑' n : ℕ, f (n : ℤ)) := hZval
    _ ≤ 2 * (2 * K ^ (1 - (j : ℝ))) := by linarith
    _ = 4 * K ^ (1 - (j : ℝ)) := by ring

end Commons.Analysis.PSeries