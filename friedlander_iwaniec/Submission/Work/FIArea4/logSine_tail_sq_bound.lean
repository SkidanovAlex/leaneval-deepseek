import Mathlib

namespace Work.FIArea4

open scoped Topology
open Filter

/-- For `N ≥ 1`, the tail `∑_{k≥0} 1/(N+1+k)²` is at most `1/N`. -/
lemma nat_tail_sq_bound (N : ℕ) (hN : 1 ≤ N) :
    (∑' k : ℕ, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  set b : ℕ → ℝ := fun k => (1 : ℝ) / ((N + k : ℕ) : ℝ) - 1 / ((N + k + 1 : ℕ) : ℝ) with hb
  have hb_sum : ∀ m : ℕ, ∑ i ∈ Finset.range m, b i
      = 1 / (N : ℝ) - 1 / ((N + m : ℕ) : ℝ) := by
    intro m
    have h := Finset.sum_range_sub' (fun i : ℕ => (1 : ℝ) / ((N + i : ℕ) : ℝ)) m
    simpa [hb, Nat.add_assoc, Nat.add_zero] using h
  have hb_nonneg : ∀ k, 0 ≤ b k := by
    intro k
    have hA : (0 : ℝ) < ((N + k : ℕ) : ℝ) := by
      have : (0 : ℕ) < N + k := by omega
      exact_mod_cast this
    have hAB : ((N + k : ℕ) : ℝ) ≤ ((N + k + 1 : ℕ) : ℝ) := by
      have : (N + k : ℕ) ≤ N + k + 1 := by omega
      exact_mod_cast this
    have := one_div_le_one_div_of_le hA hAB
    simp only [hb]
    linarith
  have hb_tendsto : Tendsto (fun m : ℕ => (1 : ℝ) / ((N + m : ℕ) : ℝ)) atTop (nhds 0) := by
    have h : Tendsto (fun m : ℕ => ((m : ℝ) + (N : ℝ))) atTop atTop :=
      tendsto_atTop_add_const_right atTop (N : ℝ) tendsto_natCast_atTop_atTop
    have h2 := h.inv_tendsto_atTop
    refine Tendsto.congr' ?_ h2
    filter_upwards with m
    simp [one_div, Nat.cast_add, add_comm]
  have hb_partial :
      Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, b i) atTop (nhds (1 / (N : ℝ))) := by
    have h := hb_tendsto.const_sub (1 / (N : ℝ))
    rw [sub_zero] at h
    refine Tendsto.congr' ?_ h
    filter_upwards with m
    rw [hb_sum m]
  have hbHS : HasSum b (1 / (N : ℝ)) :=
    (hasSum_iff_tendsto_nat_of_nonneg hb_nonneg (1 / (N : ℝ))).mpr hb_partial
  have hbsum : Summable b := hbHS.summable
  have hcomp : ∀ k : ℕ, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 2 ≤ b k := by
    intro k
    set x : ℝ := ((N + k : ℕ) : ℝ) with hxdef
    have hx : (0 : ℝ) < x := by
      rw [hxdef]
      have : (0 : ℕ) < N + k := by omega
      exact_mod_cast this
    have e1 : ((N + 1 + k : ℕ) : ℝ) = x + 1 := by
      rw [hxdef]; push_cast; ring
    have e2 : ((N + k + 1 : ℕ) : ℝ) = x + 1 := by
      rw [hxdef]; push_cast; ring
    rw [hb]
    simp only
    rw [e1, e2]
    have hsub : (1 : ℝ) / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
      field_simp
      ring
    rw [hsub, sq]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hsum_h : Summable (fun k : ℕ => (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hcomp hbsum
  calc (∑' k : ℕ, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 2)
      ≤ ∑' k : ℕ, b k := Summable.tsum_le_tsum hcomp hsum_h hbsum
    _ = 1 / (N : ℝ) := hbHS.tsum_eq

/-- The tail of the `ℓ^{-2}` sum over `ℤ`: `Σ_{|ℓ|>N} 1/ℓ² ≤ C/N`. -/
theorem logSine_tail_sq_bound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    (∑' l : ℤ, if (N : ℤ) < |l| then (1 : ℝ) / ((l : ℝ)) ^ 2 else 0) ≤ C / N := by
  refine ⟨2, by norm_num, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  let f : ℤ → ℝ := fun l => if (N : ℤ) < |l| then (1 : ℝ) / ((l : ℝ)) ^ 2 else 0
  change (∑' l : ℤ, f l) ≤ 2 / (N : ℝ)
  have hfeven : Function.Even f := by
    intro l
    simp only [f]
    rw [abs_neg]
    by_cases hc : (N : ℤ) < |l|
    · rw [if_pos hc, if_pos hc]
      congr 1
      rw [Int.cast_neg]
      ring
    · rw [if_neg hc, if_neg hc]
  have hf0 : f 0 = 0 := by
    have h : ¬ ((N : ℤ) < |(0 : ℤ)|) := by rw [abs_zero]; omega
    simp only [f]
    rw [if_neg h]
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr hbase
  have hFnonneg : ∀ n : ℕ, 0 ≤ f ((n : ℤ) + 1) := by
    intro n
    simp only [f]
    by_cases hc : (N : ℤ) < |((n : ℤ) + 1)|
    · rw [if_pos hc]; positivity
    · rw [if_neg hc]
  have hFle : ∀ n : ℕ, f ((n : ℤ) + 1) ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n
    simp only [f]
    have h1 : |((n : ℤ) + 1)| = (n : ℤ) + 1 := abs_of_nonneg (by omega)
    rw [h1]
    by_cases hc : (N : ℤ) < (n : ℤ) + 1
    · rw [if_pos hc]
      have h3 : (((n : ℤ) + 1 : ℤ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [h3]
    · rw [if_neg hc]; positivity
  have hFsumm : Summable (fun n : ℕ => f ((n : ℤ) + 1)) :=
    Summable.of_nonneg_of_le hFnonneg hFle hshift
  have hFneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hFsumm.congr (fun n => (hfeven ((n : ℤ) + 1)).symm)
  have hsplit : (∑' l : ℤ, f l) =
      ∑' n : ℕ, f ((n : ℤ) + 1) + f 0 + ∑' n : ℕ, f (-((n : ℤ) + 1)) :=
    tsum_of_add_one_of_neg_add_one hFsumm hFneg
  have hX : (∑' n : ℕ, f ((n : ℤ) + 1)) = (∑' k : ℕ, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 2) := by
    rw [← Summable.sum_add_tsum_nat_add N hFsumm]
    have hzero : (∑ i ∈ Finset.range N, f ((i : ℤ) + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [f]
      have hi' : i + 1 ≤ N := by have := Finset.mem_range.mp hi; omega
      have h1 : |((i : ℤ) + 1)| = (i : ℤ) + 1 := abs_of_nonneg (by omega)
      rw [h1]
      have h2 : ¬ ((N : ℤ) < (i : ℤ) + 1) := by
        have : (i : ℤ) + 1 ≤ (N : ℤ) := by exact_mod_cast hi'
        omega
      rw [if_neg h2]
    rw [hzero, zero_add]
    apply tsum_congr
    intro i
    simp only [f]
    have h1 : |(((i + N : ℕ) : ℤ) + 1)| = ((i + N : ℕ) : ℤ) + 1 := abs_of_nonneg (by omega)
    rw [h1]
    have h2 : (N : ℤ) < ((i + N : ℕ) : ℤ) + 1 := by
      have : (N : ℤ) ≤ ((i + N : ℕ) : ℤ) := by exact_mod_cast (Nat.le_add_left N i)
      omega
    rw [if_pos h2]
    have h3 : ((((i + N : ℕ) : ℤ) + 1 : ℤ) : ℝ) = ((N + 1 + i : ℕ) : ℝ) := by push_cast; ring
    rw [h3]
  have hneg : (∑' n : ℕ, f (-((n : ℤ) + 1))) = ∑' n : ℕ, f ((n : ℤ) + 1) :=
    tsum_congr (fun n => hfeven ((n : ℤ) + 1))
  have hbound := nat_tail_sq_bound N hN1
  calc (∑' l : ℤ, f l)
      = ∑' n : ℕ, f ((n : ℤ) + 1) + f 0 + ∑' n : ℕ, f (-((n : ℤ) + 1)) := hsplit
    _ = ∑' n : ℕ, f ((n : ℤ) + 1) + 0 + ∑' n : ℕ, f ((n : ℤ) + 1) := by rw [hf0, hneg]
    _ = 2 * (∑' n : ℕ, f ((n : ℤ) + 1)) := by ring
    _ = 2 * (∑' k : ℕ, (1 : ℝ) / ((N + 1 + k : ℕ) : ℝ) ^ 2) := by rw [hX]
    _ ≤ 2 / (N : ℝ) := by
          have h2 : (2 : ℝ) * (1 / (N : ℝ)) = 2 / (N : ℝ) := by ring
          rw [← h2]
          exact mul_le_mul_of_nonneg_left hbound (by norm_num)

end Work.FIArea4
