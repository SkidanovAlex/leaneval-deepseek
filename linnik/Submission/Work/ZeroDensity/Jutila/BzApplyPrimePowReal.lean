import Mathlib
import Submission.Work.ZeroDensity.Jutila.grahamDefs

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- **The correction term at a prime power.** For `z ≥ 1` and a prime `p`, the only divisor of `p^k`
(`k ≥ 1`) that survives in `Bz z (p^k)` is `p` itself: powers `p^j` with `j ≥ 2` carry a vanishing
Möbius factor and `1` is not `> z`. Hence `Bz z (p^k) = -log(p/z)` if `z < p`, and `0` otherwise. -/
theorem BzApplyPrimePowReal {z : ℝ} (hz : 1 ≤ z) {p k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k) :
    Work.ZeroDensity.Jutila.Bz z (p ^ k) = if z < (p : ℝ) then -Real.log ((p : ℝ) / z) else 0 := by
  have hpdvd : p ∣ p ^ k := by
    have h := pow_dvd_pow p hk
    simpa using h
  have hpne : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  unfold Work.ZeroDensity.Jutila.Bz
  by_cases hzp : z < (p : ℝ)
  · rw [if_pos hzp, Finset.sum_eq_single p]
    · have hm : (ArithmeticFunction.moebius p : ℝ) = -1 := by
        rw [ArithmeticFunction.moebius_apply_prime hp]; norm_num
      rw [hm]; ring
    · intro b hb hbp
      rw [Finset.mem_filter, Nat.mem_divisors] at hb
      obtain ⟨⟨hbdvd, _⟩, hbz⟩ := hb
      obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hbdvd
      subst hj
      have hjne1 : j ≠ 1 := by
        intro h
        exact hbp (by rw [h]; simp)
      have hjne0 : j ≠ 0 := by
        intro h
        rw [h] at hbz
        simp at hbz
        linarith
      simp [ArithmeticFunction.moebius_apply_prime_pow hp hjne0, hjne1]
    · intro hmem
      rw [Finset.mem_filter, Nat.mem_divisors] at hmem
      exact (hmem ⟨⟨hpdvd, hpne⟩, hzp⟩).elim
  · rw [if_neg hzp]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    obtain ⟨⟨hbdvd, _⟩, hbz⟩ := hb
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hbdvd
    subst hj
    have hjne0 : j ≠ 0 := by
      intro h
      rw [h] at hbz
      simp at hbz
      linarith
    have hjne1 : j ≠ 1 := by
      intro h
      rw [h] at hbz
      simp at hbz
      linarith
    simp [ArithmeticFunction.moebius_apply_prime_pow hp hjne0, hjne1]

end

end Work.ZeroDensity.Jutila
