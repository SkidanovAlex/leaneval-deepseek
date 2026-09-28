import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HP2.sum_Ico_rpow_neg_le
import Submission.Work.HP.HP2.rough_gt_w

namespace Work.HP.HP2

/-- A Möbius-sieve lower bound.

For `s > 1`, `w ≥ 1`, `K ≥ 1` and a modulus `P` divisible by every prime `≤ w`, the
truncated Möbius sum over `k ≤ K` coprime to `P` is at least
`1 - (w^{1-s}/(s-1) + w^{-s})`.

The point is elementary: every `k ≥ 2` coprime to `P` has all its prime factors `> w`,
hence `k > w`; the term `k = 1` contributes exactly `1`, and every remaining term is at
least the negative of `k^{-s}`, whose total mass beyond `w` is bounded by
`w^{-s} + w^{1-s}/(s-1)` (the `k = w`-type term plus an integral comparison). -/
theorem moebius_sieve_lower (s w K : ℝ) (hs : 1 < s) (hw : 1 ≤ w) (hK : 1 ≤ K) (P : ℕ)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ w → p ∣ P) :
    (1 : ℝ) - (w ^ (1 - s) / (s - 1) + w ^ (-s))
      ≤ ∑ k ∈ (Finset.range (⌊K⌋₊ + 1)).filter (fun k => Nat.Coprime k P),
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (k : ℝ) ^ (-s) := by
  set T : Finset ℕ := (Finset.range (⌊K⌋₊ + 1)).filter (fun k => Nat.Coprime k P) with hT
  set f : ℕ → ℝ := fun k => ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (k : ℝ) ^ (-s) with hf
  set N : ℕ := ⌊w⌋₊ + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hwN : w < (N : ℝ) := by
    rw [hN]; push_cast; exact Nat.lt_floor_add_one w
  -- `1` belongs to the index set
  have h1mem : 1 ∈ T := by
    rw [hT]
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, Nat.coprime_one_left P⟩
    have h1 : 1 ≤ ⌊K⌋₊ := Nat.le_floor (by simpa using hK)
    omega
  -- its contribution is `1`
  have hf1 : f 1 = 1 := by
    rw [hf]
    simp
  -- every term is at least `-k^{-s}`
  have hterm : ∀ k : ℕ, -(k : ℝ) ^ (-s) ≤ f k := by
    intro k
    rw [hf]
    have hm : (-1 : ℝ) ≤ ((ArithmeticFunction.moebius k : ℤ) : ℝ) := by
      have h : |ArithmeticFunction.moebius k| ≤ (1 : ℤ) := ArithmeticFunction.abs_moebius_le_one
      have : ((-1 : ℤ)) ≤ ArithmeticFunction.moebius k := (abs_le.mp h).1
      exact_mod_cast this
    have hk : (0 : ℝ) ≤ (k : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg k) _
    have hpos : 0 ≤ (((ArithmeticFunction.moebius k : ℤ) : ℝ) + 1) * (k : ℝ) ^ (-s) :=
      mul_nonneg (by linarith) hk
    nlinarith [hpos]
  -- the remaining indices are `0` or lie in `[N, ⌊K⌋₊]`
  have hsub : T.erase 1 ⊆ insert 0 (Finset.Ico N (⌊K⌋₊ + 1)) := by
    intro k hk
    have hkT : k ∈ T := Finset.mem_of_mem_erase hk
    have hkne1 : k ≠ 1 := Finset.ne_of_mem_erase hk
    rw [hT] at hkT
    obtain ⟨hkr, hkcop⟩ := Finset.mem_filter.mp hkT
    have hkle : k ≤ ⌊K⌋₊ := by have := Finset.mem_range.mp hkr; omega
    by_cases hk0 : k = 0
    · subst hk0; exact Finset.mem_insert_self 0 _
    · have hk2 : 2 ≤ k := by omega
      have hwlt : w < (k : ℝ) := rough_gt_w w P hP hk2 hkcop
      have hflt : ⌊w⌋₊ < k := (Nat.floor_lt (by linarith : (0:ℝ) ≤ w)).mpr hwlt
      exact Finset.mem_insert_of_mem (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  have h0U : (0 : ℕ) ∉ Finset.Ico N (⌊K⌋₊ + 1) := by
    simp only [Finset.mem_Ico]; omega
  have hzero : (((0:ℕ)) : ℝ) ^ (-s) = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by linarith : (-s : ℝ) ≠ 0)]
  -- total mass of `k^{-s}` over the remaining indices
  have hsum_le : ∑ k ∈ T.erase 1, (k : ℝ) ^ (-s) ≤ (N : ℝ) ^ (-s) + (N : ℝ) ^ (1 - s) / (s - 1) := by
    calc ∑ k ∈ T.erase 1, (k : ℝ) ^ (-s)
        ≤ ∑ k ∈ insert 0 (Finset.Ico N (⌊K⌋₊ + 1)), (k : ℝ) ^ (-s) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i _ _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
      _ = ∑ k ∈ Finset.Ico N (⌊K⌋₊ + 1), (k : ℝ) ^ (-s) := by
          rw [Finset.sum_insert h0U, hzero, zero_add]
      _ ≤ (N : ℝ) ^ (-s) + (N : ℝ) ^ (1 - s) / (s - 1) := sum_Ico_rpow_neg_le s hs N (⌊K⌋₊ + 1) hN1
  have hb : (N : ℝ) ^ (-s) + (N : ℝ) ^ (1 - s) / (s - 1) ≤ w ^ (-s) + w ^ (1 - s) / (s - 1) := by
    have hwpos : 0 < w := lt_of_lt_of_le one_pos hw
    have hwNle : w ≤ (N : ℝ) := le_of_lt hwN
    have hb1 : (N : ℝ) ^ (-s) ≤ w ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hwpos hwNle (by linarith : (-s:ℝ) ≤ 0)
    have hb2 : (N : ℝ) ^ (1 - s) ≤ w ^ (1 - s) :=
      Real.rpow_le_rpow_of_nonpos hwpos hwNle (by linarith : (1 - s:ℝ) ≤ 0)
    have hb3 : (N : ℝ) ^ (1 - s) / (s - 1) ≤ w ^ (1 - s) / (s - 1) :=
      div_le_div_of_nonneg_right hb2 (by linarith : (0:ℝ) ≤ s - 1)
    linarith
  have hsum_erase_ge : -(w ^ (-s) + w ^ (1 - s) / (s - 1)) ≤ ∑ k ∈ T.erase 1, f k := by
    have hneg : ∑ k ∈ T.erase 1, (-(k : ℝ) ^ (-s)) ≤ ∑ k ∈ T.erase 1, f k :=
      Finset.sum_le_sum (fun k _ => hterm k)
    rw [Finset.sum_neg_distrib] at hneg
    linarith [hneg, hsum_le, hb]
  have hsplit := Finset.add_sum_erase T f h1mem
  have hmain : (1 : ℝ) - (w ^ (1 - s) / (s - 1) + w ^ (-s)) ≤ ∑ k ∈ T, f k := by
    have heq : (w ^ (1 - s) / (s - 1) + w ^ (-s)) = (w ^ (-s) + w ^ (1 - s) / (s - 1)) := by ring
    rw [heq, ← hsplit, hf1]
    linarith [hsum_erase_ge]
  rw [show (∑ k ∈ T, f k) = ∑ k ∈ (Finset.range (⌊K⌋₊ + 1)).filter (fun k => Nat.Coprime k P),
          ((ArithmeticFunction.moebius k : ℤ) : ℝ) * (k : ℝ) ^ (-s) from by rw [hT, hf]] at hmain
  exact hmain

end Work.HP.HP2
