import Mathlib
import Submission.Work.Cert.ThetaDefs

namespace Work.Cert

/-- `thetaB` splits at the index `12`: the `12`-th partial sum `Bsum q 12` plus the tail
`∑_{n≥0} 2(-1)^{n+13} q^{(n+13)²}`.  This is purely the associativity of the (absolutely
convergent) theta series. -/
theorem thetaB_eq (q : ℂ) (hq : ‖q‖ < 1) :
    thetaB q = Bsum q 12 + ∑' n : ℕ, (2 * (-1 : ℂ) ^ (n + 13) * q ^ ((n + 13) ^ 2)) := by
  -- summability of the theta series `∑ (-1)^{n+1} q^{(n+1)²}`, by comparison with `∑ ‖q‖^n`
  have hnorm : Summable (fun n : ℕ => ‖(-1 : ℂ) ^ (n + 1) * q ^ ((n + 1) ^ 2)‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (norm_nonneg q) hq)
    have hle : ‖q‖ ^ ((n + 1) ^ 2) ≤ ‖q‖ ^ n :=
      pow_le_pow_of_le_one (norm_nonneg q) (le_of_lt hq) (by
        calc n ≤ n + 1 := Nat.le_succ n
          _ ≤ (n + 1) * (n + 1) := Nat.le_mul_self _
          _ = (n + 1) ^ 2 := (pow_two _).symm)
    simpa [norm_mul, norm_pow] using hle
  have hsum : Summable (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * q ^ ((n + 1) ^ 2)) :=
    Summable.of_norm hnorm
  have hT : thetaB q = 1 + 2 * ∑' n : ℕ, ((-1 : ℂ) ^ (n + 1) * q ^ ((n + 1) ^ 2)) := rfl
  -- the `12`-term partial sum
  have hB : Bsum q 12
      = 1 + 2 * ∑ j ∈ Finset.range 12, ((-1 : ℂ) ^ (j + 1) * q ^ ((j + 1) ^ 2)) := by
    simp only [Bsum]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  -- the tail index `n + 13 = (n + 12) + 1`
  have htail : (∑' n : ℕ, (2 * (-1 : ℂ) ^ (n + 13) * q ^ ((n + 13) ^ 2)))
      = 2 * ∑' n : ℕ, ((-1 : ℂ) ^ (n + 12 + 1) * q ^ ((n + 12 + 1) ^ 2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  have hsplit := hsum.sum_add_tsum_nat_add 12
  rw [hT, hB, htail, ← hsplit]
  ring

end Work.Cert
