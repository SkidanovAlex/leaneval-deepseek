import Mathlib
import Submission.Work.BrauerSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

theorem rho_mul_pow_order {P : Type*} [Group P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) (i : ℕ) :
    orderOf (d.rho * d.tau ^ i) = 4 ∧
    (d.rho * d.tau ^ i) * d.tau * (d.rho * d.tau ^ i)⁻¹ = d.tau⁻¹ := by
  have hn2 : 1 ≤ d.n := le_trans (by norm_num) d.hn
  -- Conjugation by `rho` inverts every power of `tau`.
  have hconj : d.rho * d.tau ^ i * d.rho⁻¹ = (d.tau ^ i)⁻¹ := by
    have h := map_pow (MulAut.conj d.rho) d.tau i
    rw [MulAut.conj_apply, MulAut.conj_apply, d.rho_conj] at h
    rw [← inv_pow]
    exact h
  have hcomm : d.tau ^ (2 ^ (d.n - 1)) * d.tau ^ i = d.tau ^ i * d.tau ^ (2 ^ (d.n - 1)) := by
    rw [← pow_add, ← pow_add, Nat.add_comm]
  have hrho : d.rho * d.rho = d.tau ^ (2 ^ (d.n - 1)) := by rw [← pow_two, d.rho_sq]
  -- `(rho * tau^i)^2` is the central involution `tau^(2^(n-1))`.
  have hsq : (d.rho * d.tau ^ i) ^ 2 = d.tau ^ (2 ^ (d.n - 1)) := by
    rw [pow_two]
    calc (d.rho * d.tau ^ i) * (d.rho * d.tau ^ i)
        = (d.rho * d.tau ^ i * d.rho⁻¹) * (d.rho * d.rho) * d.tau ^ i := by group
      _ = (d.tau ^ i)⁻¹ * d.tau ^ (2 ^ (d.n - 1)) * d.tau ^ i := by rw [hconj, hrho]
      _ = d.tau ^ (2 ^ (d.n - 1)) := by
          rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hz2 : (d.tau ^ (2 ^ (d.n - 1))) ^ 2 = 1 := by
    rw [← pow_mul]
    rw [show 2 ^ (d.n - 1) * 2 = 2 ^ d.n from by
      rw [← pow_succ, Nat.sub_add_cancel hn2]]
    rw [← d.tau_order]
    exact pow_orderOf_eq_one d.tau
  have hzne : d.tau ^ (2 ^ (d.n - 1)) ≠ 1 := by
    intro h
    have hdvd : orderOf d.tau ∣ 2 ^ (d.n - 1) := orderOf_dvd_of_pow_eq_one h
    rw [d.tau_order] at hdvd
    have hle : 2 ^ d.n ≤ 2 ^ (d.n - 1) := Nat.le_of_dvd (by positivity) hdvd
    have hlt : 2 ^ (d.n - 1) < 2 ^ d.n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  constructor
  · have hpow1 : (2 : ℕ) ^ 1 = 2 := by norm_num
    have hpow2 : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
    have hne : ¬ (d.rho * d.tau ^ i) ^ 2 ^ 1 = 1 := by
      rw [hpow1, hsq]; exact hzne
    have heq : (d.rho * d.tau ^ i) ^ 2 ^ (1 + 1) = 1 := by
      rw [hpow2, show (4 : ℕ) = 2 * 2 from by norm_num, pow_mul, hsq]
      exact hz2
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) hne heq
    rwa [hpow2] at h
  · calc (d.rho * d.tau ^ i) * d.tau * (d.rho * d.tau ^ i)⁻¹
        = d.rho * (d.tau ^ i * d.tau * (d.tau ^ i)⁻¹) * d.rho⁻¹ := by group
      _ = d.rho * d.tau * d.rho⁻¹ := by
            rw [show d.tau ^ i * d.tau * (d.tau ^ i)⁻¹ = d.tau from by group]
      _ = d.tau⁻¹ := d.rho_conj

end Work.BrauerSuzuki.Quaternion
