import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option maxHeartbeats 800000

namespace Commons.Analysis.InfiniteSum

lemma powSeries_product_hasSum_of_abs_summable {u v : ℕ → ℝ} {x s t : ℝ}
    (hu : HasSum (fun n : ℕ => u n * x ^ n) s)
    (hv : HasSum (fun n : ℕ => v n * x ^ n) t)
    (hu_abs : Summable fun n : ℕ => |u n * x ^ n|)
    (hv_abs : Summable fun n : ℕ => |v n * x ^ n|) :
    HasSum (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), u k * v (n - k)) * x ^ n) (s * t) := by
  -- Identify the inner summand with the Cauchy product of the two power series:
  -- (u k * x ^ k) * (v (n - k) * x ^ (n - k)) = u k * v (n - k) * x ^ n  for k ≤ n.
  have hsummand : ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + 1), (u k * x ^ k) * (v (n - k) * x ^ (n - k))) =
        (∑ k ∈ Finset.range (n + 1), u k * v (n - k)) * x ^ n := by
    intro n
    calc
      (∑ k ∈ Finset.range (n + 1), (u k * x ^ k) * (v (n - k) * x ^ (n - k)))
          = ∑ k ∈ Finset.range (n + 1), (u k * v (n - k)) * x ^ n := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            have hp : x ^ k * x ^ (n - k) = x ^ n := by
              rw [← pow_add x k (n - k), Nat.add_sub_of_le hk_le]
            calc
              (u k * x ^ k) * (v (n - k) * x ^ (n - k))
                  = u k * (x ^ k * (v (n - k) * x ^ (n - k))) := by ring
              _ = u k * (v (n - k) * (x ^ k * x ^ (n - k))) := by ring
              _ = u k * (v (n - k) * x ^ n) := by rw [hp]
              _ = u k * v (n - k) * x ^ n := by ring
      _ = (∑ k ∈ Finset.range (n + 1), u k * v (n - k)) * x ^ n := by
            rw [Finset.sum_mul]
  -- Absolute summability expressed with the norm, and summability of the series.
  have hu_norm : Summable (fun n : ℕ => ‖u n * x ^ n‖) := by simpa using hu_abs
  have hv_norm : Summable (fun n : ℕ => ‖v n * x ^ n‖) := by simpa using hv_abs
  -- Cauchy product of two absolutely summable ℕ-series.
  have H : HasSum (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1), (u k * x ^ k) * (v (n - k) * x ^ (n - k)))
      ((∑' n : ℕ, u n * x ^ n) * ∑' n : ℕ, v n * x ^ n) :=
    hasSum_sum_range_mul_of_summable_norm' hu_norm hu.summable hv_norm hv.summable
  -- The sums of the two series are s and t.
  have hu_tsum : (∑' n : ℕ, u n * x ^ n) = s := hu.tsum_eq
  have hv_tsum : (∑' n : ℕ, v n * x ^ n) = t := hv.tsum_eq
  -- Rewrite the Cauchy product into the requested coefficient form.
  have H' : HasSum (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), u k * v (n - k)) * x ^ n)
      ((∑' n : ℕ, u n * x ^ n) * ∑' n : ℕ, v n * x ^ n) := by
    exact H.congr_fun (fun n => (hsummand n).symm)
  rwa [hu_tsum, hv_tsum] at H'

end Commons.Analysis.InfiniteSum