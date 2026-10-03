import Mathlib

namespace Work.KMTPlan.A6

open scoped BigOperators

/-- Monotonicity of `d ↦ b / (b + d) ^ 2` on `d ≥ 0`. -/
lemma latticeQuadMass_anti {b d d' : ℝ} (hb : 0 < b) (hd0 : 0 ≤ d')
    (hd : d' ≤ d) : b / (b + d) ^ 2 ≤ b / (b + d') ^ 2 := by
  have hc : 0 < (b + d') ^ 2 := pow_pos (by linarith) 2
  have hle : (b + d') ^ 2 ≤ (b + d) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  exact div_le_div_of_nonneg_left hb.le hc hle

/-- `∑_{k ≥ 0} b / (b + k + 1) ^ 2 ≤ 1` for `b > 0`. -/
lemma sum_quad_shift_le (b : ℝ) (hb : 0 < b) :
    Summable (fun k : ℕ => b / (b + ((k : ℝ) + 1)) ^ 2) ∧
      (∑' k : ℕ, b / (b + ((k : ℝ) + 1)) ^ 2) ≤ 1 := by
  set c : ℕ → ℝ := fun k => b / (b + (k : ℝ)) - b / (b + ((k : ℝ) + 1)) with hc
  have hcq : ∀ k : ℕ, c k = b / (b + (k:ℝ)) - b / (b + ((k:ℝ) + 1)) := by
    intro k; rw [hc]
  have hc_nonneg : ∀ k : ℕ, 0 ≤ c k := by
    intro k
    rw [hcq k]
    have h1 : (0:ℝ) < b + (k:ℝ) := by positivity
    have : b / (b + ((k:ℝ) + 1)) ≤ b / (b + (k:ℝ)) :=
      div_le_div_of_nonneg_left hb.le h1 (by linarith)
    linarith
  have hle : ∀ k : ℕ, b / (b + ((k : ℝ) + 1)) ^ 2 ≤ c k := by
    intro k
    rw [hcq k]
    have h1 : (0:ℝ) < b + (k:ℝ) := by positivity
    have h2 : (0:ℝ) < b + ((k:ℝ) + 1) := by linarith
    have hce : b / (b + (k:ℝ)) - b / (b + ((k:ℝ) + 1))
        = b / ((b + (k:ℝ)) * (b + ((k:ℝ) + 1))) := by
      field_simp
      ring_nf
    rw [hce]
    apply div_le_div_of_nonneg_left hb.le
    · positivity
    · nlinarith
  have hsum_range : ∀ N : ℕ, ∑ k ∈ Finset.range N, c k = 1 - b / (b + (N : ℝ)) := by
    intro N
    have h := Finset.sum_range_sub' (fun k : ℕ => b / (b + (k : ℝ))) N
    have hc_eq : ∀ k : ℕ, c k = b / (b + (k:ℝ)) - b / (b + ((k+1 : ℕ):ℝ)) := by
      intro k
      rw [hcq k, Nat.cast_add, Nat.cast_one]
    calc ∑ k ∈ Finset.range N, c k
        = ∑ k ∈ Finset.range N, (b / (b + (k:ℝ)) - b / (b + ((k+1 : ℕ):ℝ))) :=
          Finset.sum_congr rfl (fun k _ => hc_eq k)
      _ = b / (b + ((0:ℕ):ℝ)) - b / (b + (N:ℝ)) := h
      _ = 1 - b / (b + (N:ℝ)) := by
          rw [Nat.cast_zero, add_zero, div_self (ne_of_gt hb)]
  have hz : Filter.Tendsto (fun N : ℕ => b / (b + (N:ℝ))) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun N : ℕ => (N:ℝ) + b) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right Filter.atTop b tendsto_natCast_atTop_atTop
    have hz' : Filter.Tendsto (fun N : ℕ => b / ((N:ℝ) + b)) Filter.atTop (nhds 0) :=
      Filter.Tendsto.const_div_atTop hg b
    refine hz'.congr' ?_
    filter_upwards with N
    rw [add_comm]
  have htend : Filter.Tendsto (fun N : ℕ => 1 - b / (b + (N:ℝ))) Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hz)
  have hc_sum : HasSum c 1 := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hc_nonneg 1]
    simpa only [hsum_range] using htend
  refine ⟨?_, ?_⟩
  · exact Summable.of_nonneg_of_le (fun k => by positivity) hle hc_sum.summable
  · have h := Summable.tsum_le_tsum hle
      (Summable.of_nonneg_of_le (fun k => by positivity) hle hc_sum.summable) hc_sum.summable
    rwa [hc_sum.tsum_eq] at h

/-- `∑_{k ≥ 0} b / (b + k) ^ 2 ≤ 1/b + 1` for `b > 0`. -/
lemma sum_quad_le (b : ℝ) (hb : 0 < b) :
    Summable (fun k : ℕ => b / (b + (k:ℝ)) ^ 2) ∧
      (∑' k : ℕ, b / (b + (k:ℝ)) ^ 2) ≤ 1/b + 1 := by
  obtain ⟨hB_sum, hB_le⟩ := sum_quad_shift_le b hb
  have hA_sum : Summable (fun k : ℕ => b / (b + (k:ℝ)) ^ 2) := by
    rw [← summable_nat_add_iff (f := fun k : ℕ => b / (b + (k:ℝ)) ^ 2) 1]
    simpa only [Nat.cast_add, Nat.cast_one] using hB_sum
  have htail_eq : (fun k : ℕ => b / (b + ((k+1 : ℕ) : ℝ)) ^ 2)
      = fun k : ℕ => b / (b + ((k:ℝ) + 1)) ^ 2 := by
    funext k
    simp only [Nat.cast_add, Nat.cast_one]
  have hA0 : b / (b + ((0:ℕ):ℝ)) ^ 2 = 1/b := by
    simp only [Nat.cast_zero, add_zero, sq, div_mul_eq_div_div, div_self (ne_of_gt hb),
      one_div]
  refine ⟨hA_sum, ?_⟩
  rw [hA_sum.tsum_eq_zero_add]
  rw [hA0]
  rw [htail_eq]
  linarith [hB_le]

/-- `∑_{j ∈ ℤ} b / (b + |j|) ^ 2 ≤ 1/b + 2` for `b > 0`. -/
lemma sum_quad_int (b : ℝ) (hb : 0 < b) :
    Summable (fun j : ℤ => b / (b + |(j:ℝ)|) ^ 2) ∧
      (∑' j : ℤ, b / (b + |(j:ℝ)|) ^ 2) ≤ 1/b + 2 := by
  obtain ⟨hA_sum, hA_le⟩ := sum_quad_le b hb
  obtain ⟨hB_sum, hB_le⟩ := sum_quad_shift_le b hb
  have hpos_eq : (fun n : ℕ => b / (b + |(((n:ℤ)):ℝ)|) ^ 2)
      = fun n : ℕ => b / (b + (n:ℝ)) ^ 2 := by
    funext n
    rw [Int.cast_natCast, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ))]
  have hneg_eq : (fun n : ℕ => b / (b + |(((-((n:ℤ)+1) : ℤ)):ℝ)|) ^ 2)
      = fun n : ℕ => b / (b + ((n:ℝ) + 1)) ^ 2 := by
    funext n
    have h1 : (((-((n:ℤ)+1) : ℤ)) : ℝ) = -((n:ℝ) + 1) := by
      rw [Int.cast_neg, Int.cast_add, Int.cast_one, Int.cast_natCast]
    rw [h1, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1)]
  have hpos : Summable (fun n : ℕ => b / (b + |(((n:ℤ)):ℝ)|) ^ 2) := by
    rw [hpos_eq]; exact hA_sum
  have hneg : Summable (fun n : ℕ => b / (b + |(((-((n:ℤ)+1) : ℤ)):ℝ)|) ^ 2) := by
    rw [hneg_eq]; exact hB_sum
  have hsum : Summable (fun j : ℤ => b / (b + |(j:ℝ)|) ^ 2) :=
    Summable.of_nat_of_neg_add_one (f := fun j : ℤ => b / (b + |(j:ℝ)|) ^ 2) hpos hneg
  have htsum := tsum_of_nat_of_neg_add_one (f := fun j : ℤ => b / (b + |(j:ℝ)|) ^ 2)
    hpos hneg
  refine ⟨hsum, ?_⟩
  rw [htsum, hpos_eq, hneg_eq]
  linarith [hA_le, hB_le]

theorem latticeQuadMass (b : ℝ) (hb : 0 < b) (u : ℝ) :
    Summable (fun n : ℤ => b / (b + |u - (n : ℝ)|) ^ 2) ∧
      (∑' n : ℤ, b / (b + (|u - (n : ℝ)|)) ^ 2) ≤ 4 * (1 + 1 / b) := by
  obtain ⟨hG_sum0, hG_le0⟩ := sum_quad_int b hb
  set G : ℤ → ℝ := fun j => b / (b + |(j:ℝ)|) ^ 2 with hG
  have hG_eq : ∀ j : ℤ, G j = b / (b + |(j:ℝ)|) ^ 2 := fun j => by simp only [hG]
  have hG_sum : Summable G := by rw [hG]; exact hG_sum0
  have hG_le : (∑' j : ℤ, G j) ≤ 1/b + 2 := by rw [hG]; exact hG_le0
  have hGnn : ∀ j : ℤ, 0 ≤ G j := fun j => by rw [hG]; positivity
  set m : ℤ := ⌊u⌋ with hm
  have hmle : (m:ℝ) ≤ u := by rw [hm]; exact Int.floor_le u
  have hmlt : u < (m:ℝ) + 1 := by rw [hm]; exact Int.lt_floor_add_one u
  have hpt : ∀ n : ℤ, b / (b + |u - (n:ℝ)|) ^ 2 ≤ G (n - m) + G (n - (m + 1)) := by
    intro n
    by_cases hcase : (n:ℝ) ≤ u
    · have hnm : n ≤ m := by
        have h1 : (n:ℝ) < (m:ℝ) + 1 := lt_of_le_of_lt hcase hmlt
        have h2 : n < m + 1 := by exact_mod_cast h1
        exact Int.le_of_lt_add_one h2
      have hnmr : (n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hnm
      have hdist : |((n - m : ℤ) : ℝ)| ≤ |u - (n:ℝ)| := by
        have h1 : (n:ℝ) - (m:ℝ) ≤ 0 := by linarith
        have h2 : (0:ℝ) ≤ u - (n:ℝ) := by linarith
        calc |((n - m : ℤ) : ℝ)| = |(n:ℝ) - (m:ℝ)| := by rw [Int.cast_sub]
          _ = -((n:ℝ) - (m:ℝ)) := abs_of_nonpos h1
          _ ≤ u - (n:ℝ) := by linarith
          _ = |u - (n:ℝ)| := (abs_of_nonneg h2).symm
      have hanti := latticeQuadMass_anti hb (abs_nonneg ((n - m : ℤ) : ℝ)) hdist
      have hGval : G (n - m) = b / (b + |((n - m : ℤ) : ℝ)|) ^ 2 := hG_eq (n - m)
      rw [hGval]
      exact le_trans hanti (le_add_of_nonneg_right (hGnn (n - (m + 1))))
    · have hlt : u < (n:ℝ) := lt_of_not_ge hcase
      have hmn : m < n := by
        have h1 : (m:ℝ) < (n:ℝ) := lt_of_le_of_lt hmle hlt
        exact_mod_cast h1
      have hm1n : m + 1 ≤ n := by omega
      have hdist : |((n - (m + 1) : ℤ) : ℝ)| ≤ |u - (n:ℝ)| := by
        have h1 : (0:ℝ) ≤ (n:ℝ) - (m:ℝ) - 1 := by
          have h2 : (m:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hm1n
          linarith
        have hcast : ((n - (m+1) : ℤ) : ℝ) = (n:ℝ) - (m:ℝ) - 1 := by
          rw [Int.cast_sub, Int.cast_add, Int.cast_one]
          ring
        rw [hcast, abs_of_nonneg h1, abs_of_nonpos (by linarith : u - (n:ℝ) ≤ 0)]
        linarith [hmlt]
      have hanti := latticeQuadMass_anti hb (abs_nonneg ((n - (m + 1) : ℤ) : ℝ)) hdist
      have hGval : G (n - (m + 1)) = b / (b + |((n - (m + 1) : ℤ) : ℝ)|) ^ 2 :=
        hG_eq (n - (m + 1))
      rw [hGval]
      exact le_trans hanti (le_add_of_nonneg_left (hGnn (n - m)))
  have hG1_sum : Summable (fun n : ℤ => G (n - m)) := by
    have h := (Equiv.summable_iff (Equiv.subRight m) (f := G)).mpr hG_sum
    change Summable (fun n : ℤ => G ((Equiv.subRight m) n)) at h
    simpa only [Equiv.subRight_apply] using h
  have hG2_sum : Summable (fun n : ℤ => G (n - (m + 1))) := by
    have h := (Equiv.summable_iff (Equiv.subRight (m + 1)) (f := G)).mpr hG_sum
    change Summable (fun n : ℤ => G ((Equiv.subRight (m + 1)) n)) at h
    simpa only [Equiv.subRight_apply] using h
  have hG1_tsum : (∑' n : ℤ, G (n - m)) = ∑' j : ℤ, G j := by
    simpa only [Equiv.subRight_apply] using Equiv.tsum_eq (Equiv.subRight m) G
  have hG2_tsum : (∑' n : ℤ, G (n - (m + 1))) = ∑' j : ℤ, G j := by
    simpa only [Equiv.subRight_apply] using Equiv.tsum_eq (Equiv.subRight (m + 1)) G
  have hH_sum : Summable (fun n : ℤ => G (n - m) + G (n - (m + 1))) := hG1_sum.add hG2_sum
  have hH_tsum : (∑' n : ℤ, (G (n - m) + G (n - (m + 1)))) = 2 * (∑' j : ℤ, G j) := by
    rw [Summable.tsum_add hG1_sum hG2_sum, hG1_tsum, hG2_tsum]
    ring
  have hf_sum : Summable (fun n : ℤ => b / (b + |u - (n:ℝ)|) ^ 2) := by
    apply Summable.of_nonneg_of_le (f := fun n : ℤ => G (n - m) + G (n - (m + 1)))
    · intro n; positivity
    · intro n; exact hpt n
    · exact hH_sum
  refine ⟨hf_sum, ?_⟩
  have hle : (∑' n : ℤ, b / (b + |u - (n:ℝ)|) ^ 2)
      ≤ ∑' n : ℤ, (G (n - m) + G (n - (m + 1))) :=
    Summable.tsum_le_tsum hpt hf_sum hH_sum
  have hfin : (∑' n : ℤ, (G (n - m) + G (n - (m + 1)))) ≤ 4 * (1 + 1 / b) := by
    rw [hH_tsum]
    have h2b : 2 * (1/b + 2) ≤ 4 * (1 + 1/b) := by
      have h : (0:ℝ) ≤ 1/b := by positivity
      linarith
    linarith [hG_le, h2b]
  linarith [hle, hfin]

end Work.KMTPlan.A6
