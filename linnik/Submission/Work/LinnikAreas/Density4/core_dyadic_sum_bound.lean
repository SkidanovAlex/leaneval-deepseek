import Mathlib
import Submission.Work.LinnikAreas.Density4.harmonic_block_bound
import Submission.Work.LinnikAreas.Density4.dyadic_log_series_bound
import Submission.Work.LinnikAreas.Density4.sum_Icc_antitone_blocks
import Submission.Work.LinnikAreas.Density4.div_pow_le

namespace Work.LinnikAreas.Density4

/-- The per-annulus bound.  For the dyadic annulus `A < m ≤ B` with
`A = N / 2^(j+1)` and `B = N / 2^j` (so `N / m ≥ 2^j` and `B ≤ 2 A + 1`), the
sum of `(1/m)·(log(2 + N/m))^{-2}` is at most `(log 3)·(log(2 + 2^j))^{-2}`. -/
theorem core_dyadic_block_bound (N j : ℕ) :
    ∑ m ∈ Finset.Icc (N / 2^(j+1) + 1) (N / 2^j),
        (1 : ℝ) / (m : ℝ) * (Real.log (2 + (N : ℝ) / (m : ℝ))) ^ (-2 : ℝ)
      ≤ Real.log 3 * (Real.log (2 + (2 : ℝ)^j)) ^ (-2 : ℝ) := by
  generalize hA : N / 2^(j+1) = A
  generalize hB : N / 2^j = B
  have hlogbase : (1:ℝ) < 2 + (2:ℝ)^j := by
    have h : (1:ℝ) ≤ (2:ℝ)^j := by exact_mod_cast (Nat.one_le_two_pow (n := j))
    linarith
  have hgle : 0 ≤ (Real.log (2 + (2:ℝ)^j)) ^ (-2:ℝ) :=
    le_of_lt (Real.rpow_pos_of_pos (Real.log_pos hlogbase) _)
  have hlog3 : 1 ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)).mpr (le_of_lt Real.exp_one_lt_three)
  have hB2A1 : B ≤ 2*A + 1 := by rw [← hB, ← hA]; exact div_pow_le N j
  by_cases hA0 : A = 0
  · have hBle : B ≤ 1 := by omega
    rcases (show B = 0 ∨ B = 1 by omega) with hB0 | hB1
    · rw [hA0, hB0, Finset.Icc_eq_empty (by omega : ¬ (0 + 1 : ℕ) ≤ 0), Finset.sum_empty]
      exact mul_nonneg (le_of_lt (Real.log_pos (by norm_num : (1:ℝ) < 3))) hgle
    · have hNB : 2^j ≤ N := by
        have hh := Nat.div_mul_le_self N (2^j)
        rw [hB, hB1, one_mul] at hh
        exact hh
      have hlogle : Real.log (2 + (2:ℝ)^j) ≤ Real.log (2 + (N:ℝ)) := by
        apply Real.log_le_log
        · linarith
        · have h2 : (2:ℝ)^j ≤ (N:ℝ) := by exact_mod_cast hNB
          linarith
      have hterm : (Real.log (2 + (N:ℝ)))^(-2:ℝ) ≤ (Real.log (2 + (2:ℝ)^j))^(-2:ℝ) :=
        Real.rpow_le_rpow_of_nonpos (Real.log_pos hlogbase) hlogle (by norm_num)
      rw [hA0, hB1]
      simp only [Nat.zero_add, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, div_one,
        one_mul]
      calc (Real.log (2 + (N:ℝ)))^(-2:ℝ)
          ≤ (Real.log (2 + (2:ℝ)^j))^(-2:ℝ) := hterm
        _ ≤ Real.log 3 * (Real.log (2 + (2:ℝ)^j))^(-2:ℝ) := le_mul_of_one_le_left hgle hlog3
  · have hA1 : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr hA0
    have hharm : ∑ m ∈ Finset.Icc (A+1) B, (1:ℝ)/(m:ℝ) ≤ Real.log 3 :=
      harmonic_block_bound A B hA1 hB2A1
    have hper : ∀ m ∈ Finset.Icc (A+1) B,
        (1:ℝ)/(m:ℝ) * (Real.log (2 + (N:ℝ)/(m:ℝ)))^(-2:ℝ)
          ≤ (1:ℝ)/(m:ℝ) * (Real.log (2 + (2:ℝ)^j))^(-2:ℝ) := by
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
      have hm0 : 0 < m := by omega
      have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm0
      have hBcast : (B:ℝ) ≤ (N:ℝ)/(2:ℝ)^j := by
        rw [← hB]
        have h := Nat.cast_div_le (α := ℝ) (m := N) (n := 2^j)
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
      have hmreal : (m:ℝ) ≤ (N:ℝ)/(2:ℝ)^j := le_trans (by exact_mod_cast hm2) hBcast
      have hNm : (2:ℝ)^j ≤ (N:ℝ)/(m:ℝ) := by
        rw [le_div_iff₀ hmpos]
        have h2 : (m:ℝ) * (2:ℝ)^j ≤ (N:ℝ) :=
          (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^j)).mp hmreal
        nlinarith [h2]
      have hlogge : Real.log (2 + (2:ℝ)^j) ≤ Real.log (2 + (N:ℝ)/(m:ℝ)) := by
        apply Real.log_le_log
        · linarith
        · linarith
      have hpow := Real.rpow_le_rpow_of_nonpos (Real.log_pos hlogbase) hlogge
        (by norm_num : (-2:ℝ) ≤ 0)
      have hnn : (0:ℝ) ≤ (1:ℝ)/(m:ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hpow hnn
    have hsum := Finset.sum_le_sum hper
    have hfac : ∑ m ∈ Finset.Icc (A+1) B, (1:ℝ)/(m:ℝ) * (Real.log (2 + (2:ℝ)^j))^(-2:ℝ)
        = (∑ m ∈ Finset.Icc (A+1) B, (1:ℝ)/(m:ℝ)) * (Real.log (2 + (2:ℝ)^j))^(-2:ℝ) :=
      (Finset.sum_mul _ _ _).symm
    calc ∑ m ∈ Finset.Icc (A+1) B, (1:ℝ)/(m:ℝ) * (Real.log (2 + (N:ℝ)/(m:ℝ)))^(-2:ℝ)
        ≤ ∑ m ∈ Finset.Icc (A+1) B, (1:ℝ)/(m:ℝ) * (Real.log (2 + (2:ℝ)^j))^(-2:ℝ) := hsum
      _ = (∑ m ∈ Finset.Icc (A+1) B, (1:ℝ)/(m:ℝ)) * (Real.log (2 + (2:ℝ)^j))^(-2:ℝ) := hfac
      _ ≤ Real.log 3 * (Real.log (2 + (2:ℝ)^j))^(-2:ℝ) := mul_le_mul_of_nonneg_right hharm hgle

/-- The dyadic "core" sum of the harmonic weight with a log-power saving is bounded uniformly in `N`: `∃ K, ∀ N, Σ_{m=1}^{N} (1/m)·(log(2+N/m))^{-2} ≤ K`.

Split `Icc 1 N` into the annuli `N/2^{j+1} < m ≤ N/2^j` (`j = 0,…,log₂ N`); on the `j`-th one, `N/m ≥ 2^j`, so `(log(2+N/m))^{-2} ≤ (log(2+2^j))^{-2}`, while `Σ 1/m ≤ log 3` there (the annulus is `(a,b]` with `b ≤ 2a+1` and `a ≥ 1`, so `Σ_{m=a+1}^{b} 1/m ≤ log(b/a) ≤ log 3`). Hence the core sum is at most `(log 3)·Σ_{j≥0} (log(2+2^j))^{-2}`, and that series converges: the `j=0` term is `(log 3)^{-2} ≤ 1` and for `j ≥ 1` it is `≤ (j log 2)^{-2} ≤ 4/j²` (using `Real.log_two_gt_d9`), so `Σ_j (log(2+2^j))^{-2} ≤ 9` and e.g. `K := 10` works. -/
theorem core_dyadic_sum_bound : ∃ K : ℝ, ∀ N : ℕ,
    (∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) *
        (Real.log (2 + (N : ℝ) / (m : ℝ))) ^ (-2 : ℝ)) ≤ K := by
  refine ⟨20, fun N => ?_⟩
  have ha : Antitone (fun j : ℕ => N / 2^j) := by
    intro i k hik
    exact Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num : 0 < 2) hik) (by positivity)
  have hM : N / 2^(N+1) = 0 := by
    apply Nat.div_eq_of_lt
    exact lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ N))
  have hpart : (∑ m ∈ Finset.Icc 1 N, (1:ℝ)/(m:ℝ) *
        (Real.log (2 + (N:ℝ)/(m:ℝ)))^(-2:ℝ))
      = ∑ j ∈ Finset.range (N+1), ∑ m ∈ Finset.Icc (N/2^(j+1)+1) (N/2^j),
          (1:ℝ)/(m:ℝ) * (Real.log (2 + (N:ℝ)/(m:ℝ)))^(-2:ℝ) := by
    have hh := sum_Icc_antitone_blocks (fun j : ℕ => N / 2^j) ha
      (fun m => (1:ℝ)/(m:ℝ) * (Real.log (2 + (N:ℝ)/(m:ℝ)))^(-2:ℝ)) (N+1) hM
    simpa only [pow_zero, Nat.div_one] using hh
  rw [hpart]
  calc ∑ j ∈ Finset.range (N+1), ∑ m ∈ Finset.Icc (N/2^(j+1)+1) (N/2^j),
          (1:ℝ)/(m:ℝ) * (Real.log (2 + (N:ℝ)/(m:ℝ)))^(-2:ℝ)
      ≤ ∑ j ∈ Finset.range (N+1), Real.log 3 * (Real.log (2 + (2:ℝ)^j))^(-2:ℝ) :=
        Finset.sum_le_sum (fun j _ => core_dyadic_block_bound N j)
    _ = Real.log 3 * ∑ j ∈ Finset.range (N+1), (Real.log (2 + (2:ℝ)^j))^(-2:ℝ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log 3 * 9 :=
        mul_le_mul_of_nonneg_left (dyadic_log_series_bound N)
          (le_of_lt (Real.log_pos (by norm_num : (1:ℝ) < 3)))
    _ ≤ 20 := by
        have h3 : Real.log 3 < 2 := by
          have := Real.log_lt_sub_one_of_pos (x := 3) (by norm_num) (by norm_num)
          linarith
        nlinarith

end Work.LinnikAreas.Density4
