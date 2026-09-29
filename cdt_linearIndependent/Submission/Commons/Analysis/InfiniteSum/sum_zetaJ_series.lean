import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries

namespace Commons.Analysis.InfiniteSum

open Filter
open scoped Topology

/-- The sequence `b n = 1/(n+1)`, the natural telescoping sequence. -/
private noncomputable def b (n : ℕ) : ℝ := (1 : ℝ) / ((n : ℝ) + 1)

private lemma b_cast1 (n : ℕ) : (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 2) := by
  push_cast; ring

private lemma b_cast2 (n : ℕ) : (((n + 2 : ℕ) : ℝ) + 1) = ((n : ℝ) + 3) := by
  push_cast; ring

/-- Closed form of the partial sums of `2/((n+1)(n+3))`, via telescoping. -/
private lemma partial_sum (N : ℕ) :
    ∑ n ∈ Finset.range N, (2 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3))
      = (1 - 1 / ((N : ℝ) + 1)) + (1 / 2 - 1 / ((N : ℝ) + 2)) := by
  have hAF : ∀ n : ℕ, (2 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3)) = b n - b (n + 2) := by
    intro n
    simp only [b]
    rw [b_cast2 n]
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : ((n : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring
  have hsplit : ∀ n : ℕ,
      b n - b (n + 2) = (b n - b (n + 1)) + (b (n + 1) - b (n + 2)) := by
    intro n; ring
  calc ∑ n ∈ Finset.range N, (2 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3))
      = ∑ n ∈ Finset.range N, (b n - b (n + 2)) :=
          Finset.sum_congr rfl (fun n _ => hAF n)
    _ = ∑ n ∈ Finset.range N, ((b n - b (n + 1)) + (b (n + 1) - b (n + 2))) :=
          Finset.sum_congr rfl (fun n _ => hsplit n)
    _ = ∑ n ∈ Finset.range N, (b n - b (n + 1))
          + ∑ n ∈ Finset.range N, (b (n + 1) - b ((n + 1) + 1)) :=
          Finset.sum_congr rfl (fun n _ => by rw [show n + 2 = (n + 1) + 1 by omega])
          |> fun h => h.trans Finset.sum_add_distrib
    _ = (b 0 - b N) + (b 1 - b (N + 1)) := by
          rw [Finset.sum_range_sub' b N, Finset.sum_range_sub' (fun n => b (n + 1)) N]
    _ = (1 - 1 / ((N : ℝ) + 1)) + (1 / 2 - 1 / ((N : ℝ) + 2)) := by
          simp only [b, b_cast1 N]
          norm_num

/-- The series `∑ 2/((n+1)(n+3))` sums to `3/2`. -/
private lemma hasSum_A :
    HasSum (fun n : ℕ => (2 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3))) (3 / 2) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg
    (f := fun n : ℕ => (2 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3)))
    (fun n => by positivity) (3 / 2)).mpr ?_
  have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 2)) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun N : ℕ => (1 : ℝ) / (((N + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
    refine hcomp.congr (fun N => ?_)
    push_cast
    ring_nf
  have hlim : Tendsto (fun N : ℕ => (1 - 1 / ((N : ℝ) + 1)) + (1 / 2 - 1 / ((N : ℝ) + 2)))
      atTop (𝓝 (3 / 2)) := by
    have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).add
      ((tendsto_const_nhds (x := (1 / 2 : ℝ))).sub h2)
    have hval : ((1 : ℝ) - 0) + (1 / 2 - 0) = 3 / 2 := by norm_num
    rw [hval] at hh
    simpa using hh
  exact hlim.congr' (Filter.Eventually.of_forall (fun N => (partial_sum N).symm))

theorem sum_zetaJ_series :
    (∑' n : ℕ, (4 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3) ^ 2))
      = 4 - 2 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
  have hq : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr hbase
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hR : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 3) ^ 2) := by
    have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 3).mpr hbase
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  have hA : Summable (fun n : ℕ => (2 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3))) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hq.mul_left 2)
    · positivity
    · have hle : (1 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3)) ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
        apply one_div_le_one_div_of_le (show (0 : ℝ) < ((n : ℝ) + 1) ^ 2 by positivity)
        nlinarith [show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity]
      have hL : (2 : ℝ) * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 3)))
          = (2 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3)) := by rw [← mul_div_assoc, mul_one]
      rw [← hL]
      exact mul_le_mul_of_nonneg_left hle (by norm_num)
  have hB : Summable (fun n : ℕ => 2 * (1 / ((n : ℝ) + 3) ^ 2)) := hR.mul_left 2
  have hAsum : (∑' n : ℕ, (2 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3))) = 3 / 2 :=
    hasSum_A.tsum_eq
  have hRsum : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 3) ^ 2)
      = (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) - 1 - 1 / 4 := by
    have hshift : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 3) ^ 2)
        = ∑' n : ℕ, (1 : ℝ) / ((((n + 1 + 1 : ℕ)) : ℝ) + 1) ^ 2 := by
      apply tsum_congr
      intro n
      push_cast
      ring
    have hq1 : Summable (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + 1) ^ 2) :=
      (summable_nat_add_iff 1).mpr hq
    have h1 : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)
        = 1 + ∑' n : ℕ, (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + 1) ^ 2 := by
      simpa using hq.tsum_eq_zero_add
    have h2 : (∑' n : ℕ, (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) + 1) ^ 2)
        = 1 / 4 + ∑' n : ℕ, (1 : ℝ) / ((((n + 1 + 1 : ℕ)) : ℝ) + 1) ^ 2 := by
      have h := hq1.tsum_eq_zero_add
      have hconst : (1 : ℝ) / ((↑(0 + 1 : ℕ) : ℝ) + 1) ^ 2 = 1 / 4 := by norm_num
      rw [hconst] at h
      exact h
    rw [hshift]
    linarith
  have hp : ∀ n : ℕ,
      (4 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3) ^ 2)
        = (2 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3)) - 2 * (1 / ((n : ℝ) + 3) ^ 2) := by
    intro n
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : ((n : ℝ) + 3) ≠ 0 := by positivity
    field_simp
    ring
  calc (∑' n : ℕ, (4 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3) ^ 2))
      = ∑' n : ℕ,
          ((2 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3)) - 2 * (1 / ((n : ℝ) + 3) ^ 2)) := by
          apply tsum_congr
          intro n
          exact hp n
    _ = (∑' n : ℕ, (2 : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 3)))
          - (∑' n : ℕ, 2 * (1 / ((n : ℝ) + 3) ^ 2)) :=
          Summable.tsum_sub hA hB
    _ = 3 / 2 - 2 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 3) ^ 2) := by
          rw [hAsum, tsum_mul_left]
    _ = 4 - 2 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
          rw [hRsum]; ring

end Commons.Analysis.InfiniteSum