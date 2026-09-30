import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- For `n ≥ 1` and `Y ≥ 1`: if the prime factors of `n` that are `≥ Y` number `k`, then
`k * log Y ≤ log n`. Indeed their product divides `n` (as it is a subproduct of `∏_{p | n} p`)
and dominates `Y ^ k`, so `Y ^ k ≤ n`. -/
lemma card_primeFactors_filter_le_mul_log (n Y : ℕ) (hn : 1 ≤ n) (hY : 1 ≤ Y) :
    ((n.primeFactors.filter (fun p => Y ≤ p)).card : ℝ) * Real.log Y ≤ Real.log n := by
  set S := n.primeFactors.filter (fun p => Y ≤ p) with hS
  -- Each prime in `S` is at least `Y`, hence `Y ^ |S| ≤ ∏_{p ∈ S} p`.
  have h1 : Y ^ S.card ≤ S.prod id :=
    Finset.pow_card_le_prod S id Y (fun p hp => (Finset.mem_filter.mp hp).2)
  -- The subproduct over `S` divides the full product over `n.primeFactors`,
  -- which in turn divides `n`.
  have h2 : S.prod id ∣ n.primeFactors.prod id :=
    Finset.prod_dvd_prod_of_subset S n.primeFactors id (Finset.filter_subset _ _)
  have h3 : n.primeFactors.prod id ∣ n := Nat.prod_primeFactors_dvd n
  have h4 : Y ^ S.card ≤ n :=
    Nat.le_of_dvd (by omega) (dvd_trans h2 h3) |> le_trans h1
  -- Transfer to the reals and take logarithms.
  have h5 : ((Y : ℝ) ^ S.card) ≤ (n : ℝ) := by exact_mod_cast h4
  have h6 : Real.log ((Y : ℝ) ^ S.card) ≤ Real.log n :=
    Real.log_le_log (by positivity) h5
  rwa [Real.log_pow] at h6

end Work.BMF
