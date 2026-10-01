import Mathlib

namespace Commons.Nat

/-- Pure sum identity: peeling the `j = 0` term of the defining sum and
reindexing by `j ↦ j+1` relates the sum at `n` to the sums at `n-2`. -/
private lemma sum_step {q : ℕ} (SF : ℕ → ℕ) (n : ℕ) (hn : 2 ≤ n) :
    (∑ j ∈ Finset.range (n / 2), q ^ (j + 1) * SF (n - 2 * (j + 1))) =
      q * SF (n - 2) +
        q * (∑ j ∈ Finset.range ((n - 2) / 2), q ^ (j + 1) * SF ((n - 2) - 2 * (j + 1))) := by
  have hn1 : 1 ≤ n / 2 := by omega
  let m : ℕ := n / 2 - 1
  have hm : n / 2 = m + 1 := by
    dsimp [m]
    omega
  have hdiv : m = (n - 2) / 2 := by
    dsimp [m]
    omega
  rw [hm]
  rw [Finset.sum_range_succ' (fun k => q ^ (k + 1) * SF (n - 2 * (k + 1))) m]
  -- now: (∑ k in range m, q ^ ((k+1)+1) * SF (n - 2 * ((k+1)+1))) + q ^ (0+1) * SF (n - 2*(0+1))
  --    = q * SF (n - 2) + q * (∑ j in range ((n-2)/2), q ^ (j+1) * SF ((n-2) - 2*(j+1)))
  have hf0 : q ^ (0 + 1) * SF (n - 2 * (0 + 1)) = q * SF (n - 2) := by
    norm_num
  rw [hf0]
  rw [add_comm]
  -- goal: q * SF(n-2) + (∑ k in range m, q^((k+1)+1) * SF (n - 2*((k+1)+1)))
  --     = q * SF(n-2) + q * (∑ ...)
  have hsum : (∑ k ∈ Finset.range m, q ^ ((k + 1) + 1) * SF (n - 2 * ((k + 1) + 1))) =
      q * (∑ k ∈ Finset.range ((n - 2) / 2), q ^ (k + 1) * SF ((n - 2) - 2 * (k + 1))) := by
    rw [← hdiv]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have harg : n - 2 * ((k + 1) + 1) = (n - 2) - 2 * (k + 1) := by omega
    rw [harg]
    have hpow : q ^ ((k + 1) + 1) = q * q ^ (k + 1) := pow_succ' q (k + 1)
    rw [hpow]
    ring
  rw [hsum]

theorem squarefree_count_closed {q : ℕ} {SF : ℕ → ℕ}
    (hSF0 : SF 0 = 1) (hSF1 : SF 1 = q)
    (hrec : ∀ n : ℕ, 2 ≤ n →
      q ^ n = SF n + ∑ j ∈ Finset.range (n / 2), q ^ (j + 1) * SF (n - 2 * (j + 1))) :
    ∀ n : ℕ, 2 ≤ n → SF n = q ^ n - q ^ (n - 1) := by
  intro n hn
  have hn_cases : n = 2 ∨ n = 3 ∨ 4 ≤ n := by omega
  rcases hn_cases with rfl | rfl | hn4
  · -- n = 2
    have hsum2 : (∑ j ∈ Finset.range (2 / 2), q ^ (j + 1) * SF (2 - 2 * (j + 1))) = q := by
      norm_num [hSF0]
    have h2 := hrec 2 (by omega)
    rw [hsum2] at h2
    rw [show 2 - 1 = 1 by omega]
    rw [pow_one]
    rw [h2]
    rw [Nat.add_sub_cancel]
  · -- n = 3
    have hsum3 : (∑ j ∈ Finset.range (3 / 2), q ^ (j + 1) * SF (3 - 2 * (j + 1))) = q ^ 2 := by
      norm_num [hSF1]
      exact (pow_two q).symm
    have h3 := hrec 3 (by omega)
    rw [hsum3] at h3
    rw [show 3 - 1 = 2 by omega]
    rw [h3]
    rw [Nat.add_sub_cancel]
  · -- n ≥ 4
    have hrec_n := hrec n hn
    have hrec_n2 := hrec (n - 2) (by omega : 2 ≤ n - 2)
    have hstep := sum_step (q := q) SF n hn
    have hpowstep : q * q ^ (n - 2) = q ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h1 : q ^ n = SF n + q ^ (n - 1) := by
      rw [hrec_n, hstep]
      rw [← Nat.mul_add]
      rw [← hrec_n2]
      rw [hpowstep]
    rw [h1]
    rw [Nat.add_sub_cancel]

end Commons.Nat
