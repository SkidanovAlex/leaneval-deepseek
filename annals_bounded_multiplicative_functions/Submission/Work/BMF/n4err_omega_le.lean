import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- **`ω(q) ≤ log q / log 2`.**  Since every prime factor of `q` is at least `2`, the product
`∏_{p | q} p` dominates `2 ^ ω(q)`; this product divides `q`, so `2 ^ ω(q) ≤ q`, and taking
logarithms gives `ω(q) · log 2 ≤ log q`. -/
theorem n4err_omega_le (q : ℕ) (hq : 1 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ Real.log q / Real.log 2 := by
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `2 ^ ω(q) ≤ q`
  have h1 : 2 ^ q.primeFactors.card ≤ q := by
    have hle : 2 ^ (q.primeFactors.filter (fun p => 2 ≤ p)).card
        ≤ (q.primeFactors.filter (fun p => 2 ≤ p)).prod id :=
      Finset.pow_card_le_prod (q.primeFactors.filter (fun p => 2 ≤ p)) id 2
        (fun p hp => (Finset.mem_filter.mp hp).2)
    have hfil : q.primeFactors.filter (fun p => 2 ≤ p) = q.primeFactors :=
      Finset.filter_true_of_mem
        (fun p hp => Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
    rw [hfil] at hle
    exact le_trans hle (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q))
  -- take logarithms
  have h2 : ((2 : ℝ) ^ q.primeFactors.card) ≤ (q : ℝ) := by exact_mod_cast h1
  have h3 : Real.log ((2 : ℝ) ^ q.primeFactors.card) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  exact (le_div_iff₀ hL2).mpr h3

end Work.BMF
