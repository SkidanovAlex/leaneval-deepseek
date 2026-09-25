import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- Geometric tail bound in `NNReal`: for every `M`,
`∑_{m<M} (1/4)^{M-m} = 1/4 + (1/4)^2 + … + (1/4)^M ≤ 1/3`.
Proved by induction using the self-similarity `S_{n+1} = (1/4)·S_n + 1/4`. -/
private lemma quarter_geom_tail_le (M : ℕ) :
    (∑ m ∈ Finset.range M, (1 / 4 : NNReal) ^ (M - m)) ≤ 1 / 3 := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hcongr : ∀ m ∈ Finset.range n,
        (1 / 4 : NNReal) ^ (n + 1 - m) = (1 / 4) * (1 / 4 : NNReal) ^ (n - m) := by
      intro m hm
      have hmle : m ≤ n := le_of_lt (Finset.mem_range.mp hm)
      rw [show n + 1 - m = (n - m) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum]
    have hn1 : (1 / 4 : NNReal) ^ (n + 1 - n) = 1 / 4 := by
      rw [show n + 1 - n = 1 by omega, pow_one]
    rw [hn1]
    calc (1 / 4 : NNReal) * (∑ m ∈ Finset.range n, (1 / 4) ^ (n - m)) + 1 / 4
        ≤ (1 / 4 : NNReal) * (1 / 3) + 1 / 4 := by gcongr
      _ = 1 / 3 := by norm_num

theorem binom_half_pow_sum_le {M : ℕ} (hM : 2 ≤ M) :
    (∑ m ∈ Finset.range M, ((2 * M).choose m : NNReal) * (1 / 4 : NNReal) ^ (2 * M - m))
      ≤ 1 / 3 := by
  calc (∑ m ∈ Finset.range M, ((2 * M).choose m : NNReal) * (1 / 4 : NNReal) ^ (2 * M - m))
      ≤ ∑ m ∈ Finset.range M, (1 / 4 : NNReal) ^ (M - m) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmle : m ≤ M := le_of_lt (Finset.mem_range.mp hm)
        -- `(2*M).choose m ≤ 4^M` as naturals, since `4^M = 2^(2*M)` dominates every binomial coefficient.
        have hchoose : ((2 * M).choose m : NNReal) ≤ (4 : NNReal) ^ M := by
          have hn : (2 * M).choose m ≤ 4 ^ M := by
            have h1 : (2 * M).choose m ≤ 2 ^ (2 * M) := Nat.choose_le_two_pow (2 * M) m
            have h2 : (2 : ℕ) ^ (2 * M) = 4 ^ M := by
              rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
            exact le_trans h1 (le_of_eq h2)
          exact_mod_cast hn
        -- `4^M · (1/4)^(2M-m) = (1/4)^(M-m)`.
        have hpow : (4 : NNReal) ^ M * (1 / 4 : NNReal) ^ (2 * M - m) = (1 / 4 : NNReal) ^ (M - m) := by
          rw [show 2 * M - m = M + (M - m) by omega, pow_add]
          rw [← mul_assoc, ← mul_pow]
          rw [show (4 : NNReal) * (1 / 4) = 1 by norm_num, one_pow, one_mul]
        calc ((2 * M).choose m : NNReal) * (1 / 4 : NNReal) ^ (2 * M - m)
            ≤ (4 : NNReal) ^ M * (1 / 4 : NNReal) ^ (2 * M - m) := by gcongr
          _ = (1 / 4 : NNReal) ^ (M - m) := hpow
    _ ≤ 1 / 3 := quarter_geom_tail_le M

end Work.BourgainPlan.IonescuWainger
