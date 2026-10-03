import Mathlib
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Commons.Data.Nat.gcd_eq_sum_totient_divisors_ne_zero

namespace Work.FIArea2.Count

open Finset

/-- For `d ≥ 1`: `∑_{n ≤ X} gcd(n,d) ≤ X · τ(d)`. -/
theorem sum_gcd_le_mul_card_divisors (d X : ℕ) (hd : 1 ≤ d) :
    (∑ n ∈ Finset.Icc 1 X, (Nat.gcd n d : ℝ)) ≤ (X : ℝ) * (d.divisors.card : ℝ) := by
  have hdne : d ≠ 0 := by omega
  -- The natural-number version of the statement.
  have hnat : (∑ n ∈ Finset.Icc 1 X, Nat.gcd n d) ≤ X * d.divisors.card := by
    -- Expand `gcd n d` as `∑_{k | d, k | n} φ k`.
    have hterm : ∀ n ∈ Finset.Icc 1 X,
        Nat.gcd n d = ∑ k ∈ d.divisors, (if k ∣ n then Nat.totient k else 0) := by
      intro n _
      rw [Commons.Data.Nat.gcd_eq_sum_totient_divisors_ne_zero (c := n) hdne,
        Finset.sum_filter]
    calc (∑ n ∈ Finset.Icc 1 X, Nat.gcd n d)
        = ∑ n ∈ Finset.Icc 1 X,
            ∑ k ∈ d.divisors, (if k ∣ n then Nat.totient k else 0) :=
          Finset.sum_congr rfl hterm
      _ = ∑ k ∈ d.divisors,
            ∑ n ∈ Finset.Icc 1 X, (if k ∣ n then Nat.totient k else 0) :=
          Finset.sum_comm
      _ = ∑ k ∈ d.divisors,
            Nat.totient k * ((Finset.Icc 1 X).filter (fun n => k ∣ n)).card := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm, Nat.cast_id]
      _ ≤ ∑ _k ∈ d.divisors, X := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk1 : 1 ≤ k := Nat.pos_of_mem_divisors hk
          have hcard : ((Finset.Icc 1 X).filter (fun n => k ∣ n)).card ≤ X / k := by
            rw [← image_mul_Icc_eq_filter hk1]
            calc ((Finset.Icc 1 (X / k)).image (fun m => k * m)).card
                ≤ (Finset.Icc 1 (X / k)).card := Finset.card_image_le
              _ = X / k := by simp
          calc Nat.totient k * ((Finset.Icc 1 X).filter (fun n => k ∣ n)).card
              ≤ Nat.totient k * (X / k) := Nat.mul_le_mul_left _ hcard
            _ ≤ k * (X / k) := Nat.mul_le_mul_right _ (Nat.totient_le k)
            _ ≤ X := Nat.mul_div_le X k
      _ = X * d.divisors.card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm, Nat.cast_id]
  have hcast : ((∑ n ∈ Finset.Icc 1 X, Nat.gcd n d : ℕ) : ℝ)
      = ∑ n ∈ Finset.Icc 1 X, (Nat.gcd n d : ℝ) := Nat.cast_sum _ _
  rw [← hcast]
  exact_mod_cast hnat

end Work.FIArea2.Count
