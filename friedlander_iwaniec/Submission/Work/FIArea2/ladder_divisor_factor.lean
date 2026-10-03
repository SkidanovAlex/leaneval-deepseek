import Mathlib
import Submission.Work.FIArea2.sum_tau_pow_le

namespace Work.FIArea2

open Finset

/-- **The divisor ladder of *FI* §9 (the step from (9.7) to the following display).**
For every `L` and `k`,
  `∑_{d ∣ L} φ(d)·τ(d)^{k+1}/d ≤ τ(L)^{k+2}`.

The elementary mechanism is a two-line estimate: for `d ∣ L` one has `φ(d) ≤ d` and `τ(d) ≤ τ(L)`,
so the `d`-th summand is at most `τ(L)^{k+1}`, and there are exactly `τ(L)` of them. -/
lemma ladder_divisor_factor (L k : ℕ) :
    (∑ d ∈ L.divisors, (Nat.totient d : ℝ) * (tauR d ^ (k + 1) / (d : ℝ)))
      ≤ tauR L ^ (k + 2) := by
  have hterm : ∀ d ∈ L.divisors,
      (Nat.totient d : ℝ) * (tauR d ^ (k + 1) / (d : ℝ)) ≤ tauR L ^ (k + 1) := by
    intro d hd
    obtain ⟨hdvd, hL0⟩ := Nat.mem_divisors.mp hd
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hL0 (Nat.zero_dvd.mp hdvd)
    have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    have hφ : (Nat.totient d : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
    have hτd : tauR d ≤ tauR L := by
      have hsub := Nat.divisors_subset_of_dvd (n := L) (m := d) hL0 hdvd
      have hcard := Finset.card_le_card hsub
      unfold tauR
      exact_mod_cast hcard
    have hnn : 0 ≤ tauR d ^ (k + 1) / (d : ℝ) :=
      div_nonneg (pow_nonneg (tauR_nonneg d) (k + 1)) (Nat.cast_nonneg d)
    have hle : (Nat.totient d : ℝ) * (tauR d ^ (k + 1) / (d : ℝ)) ≤ tauR d ^ (k + 1) := by
      calc (Nat.totient d : ℝ) * (tauR d ^ (k + 1) / (d : ℝ))
          ≤ (d : ℝ) * (tauR d ^ (k + 1) / (d : ℝ)) :=
            mul_le_mul_of_nonneg_right hφ hnn
        _ = tauR d ^ (k + 1) := by
            rw [← mul_div_assoc]
            exact mul_div_cancel_left₀ _ hdne
    exact hle.trans (pow_le_pow_left₀ (tauR_nonneg d) hτd (k + 1))
  calc (∑ d ∈ L.divisors, (Nat.totient d : ℝ) * (tauR d ^ (k + 1) / (d : ℝ)))
      ≤ ∑ d ∈ L.divisors, tauR L ^ (k + 1) := Finset.sum_le_sum hterm
    _ = (L.divisors.card : ℝ) * tauR L ^ (k + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = tauR L ^ (k + 2) := by
          rw [show (L.divisors.card : ℝ) = tauR L from rfl,
              show k + 2 = (k + 1) + 1 from by omega, pow_succ]
          ring

end Work.FIArea2
