import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Commons.Analysis.Series

open Finset

/--
Telescoping identity for the shifted series with step `1/2`:
`∑_{k<n} [N ≤ k] (1/(k-1/2) - 1/(k+1/2)) = c - [N ≤ n ? 1/(n-1/2) : c]`
where `c = [N ≤ 0 ? 1/(-1/2) : 1/(N-1/2)]`.
-/
private lemma telescope_indicator (N n : ℕ) :
    ∑ k ∈ Finset.range n,
        (if N ≤ k then (1 / ((k : ℝ) - 1/2) - 1 / ((k : ℝ) + 1/2)) else 0)
      = (if N ≤ 0 then 1 / ((0 : ℝ) - 1/2) else 1 / ((N : ℝ) - 1/2))
        - (if N ≤ n then 1 / ((n : ℝ) - 1/2) else 1 / ((N : ℝ) - 1/2)) := by
  have key : ∀ k : ℕ,
      (if N ≤ k then (1 / ((k : ℝ) - 1/2) - 1 / ((k : ℝ) + 1/2)) else 0)
        = (if N ≤ k then 1 / ((k : ℝ) - 1/2) else 1 / ((N : ℝ) - 1/2))
          - (if N ≤ k + 1 then 1 / (((k + 1 : ℕ) : ℝ) - 1/2)
              else 1 / ((N : ℝ) - 1/2)) := by
    intro k
    by_cases h : N ≤ k
    · have h2 : N ≤ k + 1 := by omega
      rw [if_pos h, if_pos h, if_pos h2]
      push_cast
      ring
    · by_cases h2 : N ≤ k + 1
      · rw [if_neg h, if_neg h, if_pos h2]
        have hk1 : k + 1 = N := by omega
        rw [hk1]
        ring
      · rw [if_neg h, if_neg h, if_neg h2]
        ring
  rw [Finset.sum_congr rfl (fun k _ => key k)]
  rw [Finset.sum_range_sub'
    (fun j : ℕ => if N ≤ j then 1 / ((j : ℝ) - 1/2) else 1 / ((N : ℝ) - 1/2))]
  norm_num

theorem tail_inv_sq_le (N : ℕ) (hN : 1 ≤ N) :
    (∑' n : ℕ, (if N ≤ n then 1 / (n : ℝ)^2 else 0)) ≤ 2 / (2 * (N : ℝ) - 1) := by
  have hNpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNhalf : (0 : ℝ) < (N : ℝ) - 1/2 := by linarith
  have hF0 : (if N ≤ 0 then 1 / ((0 : ℝ) - 1/2) else 1 / ((N : ℝ) - 1/2))
      = 2 / (2 * (N : ℝ) - 1) := by
    have h0 : ¬ (N ≤ 0) := by omega
    rw [if_neg h0]
    have hne : (2 * (N : ℝ) - 1) ≠ 0 := by linarith
    field_simp
  have hkey : ∀ n : ℕ,
      ∑ k ∈ Finset.range n, (if N ≤ k then 1 / (k : ℝ)^2 else 0)
        ≤ 2 / (2 * (N : ℝ) - 1) := by
    intro n
    have htel := telescope_indicator N n
    have hFn_nn : 0 ≤ (if N ≤ n then 1 / ((n : ℝ) - 1/2) else 1 / ((N : ℝ) - 1/2)) := by
      by_cases hn : N ≤ n
      · rw [if_pos hn]
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans hNpos (by exact_mod_cast hn)
        have hp : (0 : ℝ) < (n : ℝ) - 1/2 := by linarith
        exact div_nonneg zero_le_one (le_of_lt hp)
      · rw [if_neg hn]
        exact div_nonneg zero_le_one (le_of_lt hNhalf)
    have hterm : ∀ k ∈ Finset.range n,
        (if N ≤ k then 1 / (k : ℝ)^2 else 0)
          ≤ (if N ≤ k then (1 / ((k : ℝ) - 1/2) - 1 / ((k : ℝ) + 1/2)) else 0) := by
      intro k _
      by_cases hk : N ≤ k
      · rw [if_pos hk, if_pos hk]
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := le_trans hNpos (by exact_mod_cast hk)
        have hb : 0 < ((k : ℝ) - 1/2) * ((k : ℝ) + 1/2) := by nlinarith
        have hle : ((k : ℝ) - 1/2) * ((k : ℝ) + 1/2) ≤ (k : ℝ)^2 := by nlinarith
        calc (1 : ℝ) / (k : ℝ)^2
            ≤ 1 / (((k : ℝ) - 1/2) * ((k : ℝ) + 1/2)) :=
              one_div_le_one_div_of_le hb hle
          _ = 1 / ((k : ℝ) - 1/2) - 1 / ((k : ℝ) + 1/2) := by
              have h1 : ((k : ℝ) - 1/2) ≠ 0 := by linarith
              have h2 : ((k : ℝ) + 1/2) ≠ 0 := by linarith
              rw [div_sub_div (1 : ℝ) 1 h1 h2]
              norm_num
      · rw [if_neg hk, if_neg hk]
    calc ∑ k ∈ Finset.range n, (if N ≤ k then 1 / (k : ℝ)^2 else 0)
        ≤ ∑ k ∈ Finset.range n,
            (if N ≤ k then (1 / ((k : ℝ) - 1/2) - 1 / ((k : ℝ) + 1/2)) else 0) :=
          Finset.sum_le_sum hterm
      _ = (if N ≤ 0 then 1 / ((0 : ℝ) - 1/2) else 1 / ((N : ℝ) - 1/2))
            - (if N ≤ n then 1 / ((n : ℝ) - 1/2) else 1 / ((N : ℝ) - 1/2)) := htel
      _ ≤ 2 / (2 * (N : ℝ) - 1) := by
          rw [hF0]
          linarith
  refine Real.tsum_le_of_sum_range_le (f := fun n : ℕ => if N ≤ n then 1 / (n : ℝ)^2 else 0)
    (c := 2 / (2 * (N : ℝ) - 1)) ?_ hkey
  intro n
  by_cases h : N ≤ n
  · rw [if_pos h]
    positivity
  · rw [if_neg h]

end Commons.Analysis.Series