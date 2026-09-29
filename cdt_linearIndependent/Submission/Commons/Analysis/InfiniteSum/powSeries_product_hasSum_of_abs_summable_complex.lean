import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option maxHeartbeats 1200000

namespace Commons.Analysis.InfiniteSum

lemma powSeries_product_hasSum_of_abs_summable_complex {u v : ℕ → ℂ} {x s t : ℂ}
    (hu : HasSum (fun n : ℕ => u n * x ^ n) s)
    (hv : HasSum (fun n : ℕ => v n * x ^ n) t)
    (hu_abs : Summable fun n : ℕ => ‖u n * x ^ n‖)
    (hv_abs : Summable fun n : ℕ => ‖v n * x ^ n‖) :
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
  -- Cauchy product of two absolutely summable ℕ-series (over the normed ring ℂ).
  have H : HasSum (fun n : ℕ =>
        ∑ k ∈ Finset.range (n + 1), (u k * x ^ k) * (v (n - k) * x ^ (n - k)))
      ((∑' n : ℕ, u n * x ^ n) * ∑' n : ℕ, v n * x ^ n) :=
    hasSum_sum_range_mul_of_summable_norm' (f := fun n => u n * x ^ n) (g := fun n => v n * x ^ n)
      hu_abs hu.summable hv_abs hv.summable
  -- The sums of the two series are s and t.
  have hu_tsum : (∑' n : ℕ, u n * x ^ n) = s := hu.tsum_eq
  have hv_tsum : (∑' n : ℕ, v n * x ^ n) = t := hv.tsum_eq
  -- Rewrite the Cauchy product into the requested coefficient form.
  have H' : HasSum (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), u k * v (n - k)) * x ^ n)
      ((∑' n : ℕ, u n * x ^ n) * ∑' n : ℕ, v n * x ^ n) := by
    exact H.congr_fun (fun n => (hsummand n).symm)
  rw [hu_tsum, hv_tsum] at H'
  exact H'

end Commons.Analysis.InfiniteSum