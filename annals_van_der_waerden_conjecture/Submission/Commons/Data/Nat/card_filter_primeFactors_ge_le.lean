import Mathlib.Data.Nat.Log
import Submission.Commons.NumberTheory.Nat.prod_dvd_iff_all_dvd

open scoped BigOperators

namespace Commons.Data.Nat

/-- `Nat.log B (H ^ K) ≤ K * (Nat.log B H + 1)` for a base `B ≥ 2`. -/
private lemma log_pow_le_mul_log_add_one (B H K : ℕ) (hB : 1 < B) :
    Nat.log B (H ^ K) ≤ K * (Nat.log B H + 1) := by
  by_cases hK : K = 0
  · subst hK
    simp
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    by_cases hH : H = 0
    · subst hH
      rw [Nat.zero_pow hKpos]
      simp
    · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
      have hlt : H < B ^ (Nat.log B H + 1) := by
        simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hB H
      have hpowlt : H ^ K < (B ^ (Nat.log B H + 1)) ^ K :=
        Nat.pow_lt_pow_left hlt hK
      have hpowlt' : H ^ K < B ^ (K * (Nat.log B H + 1)) := by
        simpa [← pow_mul, Nat.mul_comm (Nat.log B H + 1) K] using hpowlt
      have hHK : H ^ K ≠ 0 := by
        exact (Nat.pow_pos (a := H) (n := K) hHpos).ne'
      exact Nat.le_of_lt
        (Nat.log_lt_of_lt_pow (y := H ^ K) (x := K * (Nat.log B H + 1)) hHK hpowlt')

theorem card_filter_primeFactors_ge_le (B z K H : ℕ) (hB : 1 < B) (hz : z ≠ 0)
    (hle : z ≤ H ^ K) :
    ((Nat.primeFactors z).filter fun p => B ≤ p).card ≤ K * (Nat.log B H + 1) := by
  let S : Finset ℕ := z.primeFactors.filter (fun p => B ≤ p)
  have hSsub : S ⊆ z.primeFactors := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hSp : ∀ p ∈ S, B ≤ p := fun p hp => (Finset.mem_filter.mp hp).2
  have hprod_dvd : (∏ p ∈ S, p) ∣ z := by
    exact (Commons.NumberTheory.Nat.prod_dvd_iff_all_dvd hSsub).mpr (by
      intro p hp
      exact Nat.dvd_of_mem_primeFactors (hSsub hp))
  have hprod_ge : B ^ S.card ≤ ∏ p ∈ S, p := by
    calc
      B ^ S.card = ∏ p ∈ S, B := (Finset.prod_const B).symm
      _ ≤ ∏ p ∈ S, p := by
        exact Finset.prod_le_prod' (f := fun _ : ℕ => B) (g := fun p : ℕ => p) (s := S) (by
          intro p hp
          exact hSp p hp)
  have hprod_le : (∏ p ∈ S, p) ≤ z := Nat.le_of_dvd (Nat.pos_of_ne_zero hz) hprod_dvd
  have hBm : B ^ S.card ≤ z := le_trans hprod_ge hprod_le
  have hBm' : B ^ S.card ≤ H ^ K := le_trans hBm hle
  have hm : S.card ≤ Nat.log B (H ^ K) := Nat.le_log_of_pow_le hB hBm'
  have hlog : Nat.log B (H ^ K) ≤ K * (Nat.log B H + 1) :=
    log_pow_le_mul_log_add_one B H K hB
  simpa [S] using (le_trans hm hlog)

end Commons.Data.Nat