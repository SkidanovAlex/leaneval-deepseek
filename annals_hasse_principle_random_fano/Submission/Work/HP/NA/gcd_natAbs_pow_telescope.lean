import Mathlib

namespace Work.HP.NA

/-- Natural-number form of the telescoping identity for `gcd n (p^r)`: the
greatest power of the prime `p` dividing `n` that is at most `p^r`, written as a
telescoping sum of the differences `p^e - p^(e-1)` over the exponents `e ≤ r`
for which `p^e ∣ n`. -/
theorem gcd_pow_telescope_nat (p r : ℕ) (hp : p.Prime) (n : ℕ) :
    Nat.gcd n (p ^ r)
      = 1 + ∑ e ∈ Finset.Ico 1 (r + 1),
          (p ^ e - p ^ (e - 1)) * (if p ^ e ∣ n then 1 else 0) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hsplit :
        (∑ e ∈ Finset.Ico 1 (r + 1 + 1),
            (p ^ e - p ^ (e - 1)) * (if p ^ e ∣ n then 1 else 0))
          = (∑ e ∈ Finset.Ico 1 (r + 1),
              (p ^ e - p ^ (e - 1)) * (if p ^ e ∣ n then 1 else 0))
            + (p ^ (r + 1) - p ^ (r + 1 - 1))
                * (if p ^ (r + 1) ∣ n then 1 else 0) :=
      Finset.sum_Ico_succ_top (by omega) _
    rw [hsplit, ← Nat.add_assoc, ← ih]
    by_cases h : p ^ (r + 1) ∣ n
    · have hpr : p ^ r ∣ n := dvd_trans (pow_dvd_pow p (Nat.le_succ r)) h
      have hgcdr : Nat.gcd n (p ^ r) = p ^ r := Nat.gcd_eq_right hpr
      have hgcdr1 : Nat.gcd n (p ^ (r + 1)) = p ^ (r + 1) := Nat.gcd_eq_right h
      rw [hgcdr1, hgcdr, ite_eq_left h, Nat.mul_one]
      have hsub : r + 1 - 1 = r := by omega
      rw [hsub, Nat.add_sub_of_le (Nat.pow_le_pow_right hp.pos (Nat.le_succ r))]
    · have hgcd_eq : Nat.gcd n (p ^ (r + 1)) = Nat.gcd n (p ^ r) := by
        apply Nat.dvd_antisymm
        · obtain ⟨k, hk_le, hk_eq⟩ :=
            (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right n (p ^ (r + 1)))
          have hkr : k ≤ r := by
            rcases Nat.lt_or_eq_of_le hk_le with hlt | heq
            · omega
            · exfalso
              have hge : Nat.gcd n (p ^ (r + 1)) = p ^ (r + 1) := by rw [hk_eq, heq]
              exact h (hge ▸ Nat.gcd_dvd_left n (p ^ (r + 1)))
          rw [hk_eq]
          exact Nat.dvd_gcd (hk_eq ▸ Nat.gcd_dvd_left n (p ^ (r + 1)))
            (pow_dvd_pow p hkr)
        · exact Nat.dvd_gcd (Nat.gcd_dvd_left n (p ^ r))
            (dvd_trans (Nat.gcd_dvd_right n (p ^ r)) (pow_dvd_pow p (Nat.le_succ r)))
      rw [hgcd_eq, ite_eq_right h, Nat.mul_zero, Nat.add_zero]

theorem gcd_natAbs_pow_telescope (p r : ℕ) (hp : p.Prime) (g : ℤ) :
    Nat.gcd g.natAbs (p ^ r)
      = 1 + ∑ e ∈ Finset.Ico 1 (r + 1),
          (p ^ e - p ^ (e - 1)) * (if (p : ℤ) ^ e ∣ g then 1 else 0) := by
  rw [gcd_pow_telescope_nat p r hp g.natAbs]
  congr 1
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have hiff : ((p : ℤ) ^ e ∣ g) ↔ (p ^ e ∣ g.natAbs) := by
    rw [← Nat.cast_pow, Int.ofNat_dvd_left]
  by_cases hc : (p : ℤ) ^ e ∣ g
  · simp only [hc, hiff.mp hc, ite_true]
  · have hc' : ¬ (p ^ e ∣ g.natAbs) := fun h => hc (hiff.mpr h)
    simp only [hc, hc', ite_false]

end Work.HP.NA
