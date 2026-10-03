import Mathlib
import Submission.Work.FIArea4.SqfreeKernel

namespace Work.FIArea4

/-- **Structure of the squarefree kernel** (for `m ≠ 0`; for `m = 0` the statement is false).
`sqPart m = Nat.findGreatest (fun t => t ^ 2 ∣ m) (Nat.sqrt m)` is the largest `t` with
`t ^ 2 ∣ m`, and `sqfreeKernel m = m / (sqPart m) ^ 2` satisfies `sqfreeKernel m * (sqPart m)^2 = m`
and is squarefree. Use `Nat.findGreatest_eq_iff` and `Nat.findGreatest_spec`, `Nat.le_sqrt`,
`Nat.div_mul_cancel`, and `Nat.squarefree_iff_prime_squarefree` (a prime square dividing
`m / sqPart m ^ 2` would give `(sqPart m * p) ^ 2 ∣ m` with `sqPart m * p > sqPart m`, contradicting
maximality). -/
theorem sqfree_kernel (m : ℕ) (hm : m ≠ 0) :
    Work.FIArea4.sqPart m ^ 2 ∣ m ∧
    (∀ t : ℕ, t ^ 2 ∣ m → t ≤ Work.FIArea4.sqPart m) ∧
    Work.FIArea4.sqfreeKernel m * Work.FIArea4.sqPart m ^ 2 = m ∧
    Work.FIArea4.sqfreeKernel m ∣ m ∧ Squarefree (Work.FIArea4.sqfreeKernel m) := by
  have hmp : 0 < m := Nat.pos_of_ne_zero hm
  have hsqrt1 : 1 ≤ Nat.sqrt m := by
    have : 0 < Nat.sqrt m := Nat.sqrt_pos.mpr hmp
    omega
  -- `1 ^ 2` divides `m` and `1 ≤ √m`, so the greatest `t ≤ √m` with `t ^ 2 ∣ m`
  -- satisfies the divisibility condition, and in particular is nonzero.
  have hP : sqPart m ^ 2 ∣ m :=
    Nat.findGreatest_spec (P := fun t => t ^ 2 ∣ m) (n := Nat.sqrt m) hsqrt1 (by simp)
  -- Maximality of `sqPart m`: any `t` with `t ^ 2 ∣ m` has `t ≤ sqPart m`.
  have hmax : ∀ t, t ^ 2 ∣ m → t ≤ sqPart m := by
    intro t ht
    have htle : t ≤ Nat.sqrt m := by
      rw [Nat.le_sqrt]
      have h : t ^ 2 ≤ m := Nat.le_of_dvd hmp ht
      simpa [pow_two] using h
    by_contra hcon
    push Not at hcon
    have hkey : Nat.findGreatest (fun s => s ^ 2 ∣ m) (Nat.sqrt m) = sqPart m := rfl
    exact (Nat.findGreatest_eq_iff.mp hkey).2.2 hcon htle ht
  have hsqm : sqfreeKernel m * sqPart m ^ 2 = m := Nat.div_mul_cancel hP
  have hdvdk : sqfreeKernel m ∣ m := Nat.div_dvd_of_dvd hP
  have hsf : Squarefree (sqfreeKernel m) := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdiv
    -- `hdiv : p * p ∣ sqfreeKernel m`, say `sqfreeKernel m = p * p * k`.
    obtain ⟨k, hk⟩ := hdiv
    have hsq1 : 1 ≤ sqPart m := by
      have := hmax 1 (by simp)
      simpa using this
    -- Then `m = (p * sqPart m) ^ 2 * k`, so `(p * sqPart m) ^ 2 ∣ m`.
    have hmeq : m = (p * sqPart m) ^ 2 * k := by
      calc m = sqfreeKernel m * sqPart m ^ 2 := hsqm.symm
        _ = (p * p * k) * sqPart m ^ 2 := by rw [hk]
        _ = (p * sqPart m) ^ 2 * k := by ring
    have hdvd : (p * sqPart m) ^ 2 ∣ m := ⟨k, hmeq⟩
    -- Maximality gives `p * sqPart m ≤ sqPart m`, hence `p ≤ 1`, contradicting primeness.
    have hle : p * sqPart m ≤ sqPart m := hmax _ hdvd
    have hp1 : p ≤ 1 := by
      refine Nat.le_of_mul_le_mul_right ?_ (lt_of_lt_of_le zero_lt_one hsq1)
      simpa using hle
    have := hp.two_le
    omega
  exact ⟨hP, hmax, hsqm, hdvdk, hsf⟩

end Work.FIArea4
