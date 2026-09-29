import Mathlib

namespace Work.TMComp.RedC7T

/-- For the (infinite) continued fraction expansion of a real number `v`, the numerator
`nums n` and denominator `dens n` of the `n`-th convergent are coprime.  Phrased for an
integer sequence `A` and a natural sequence `B` which represent `nums` and `dens` as reals.

The proof uses the determinant (Cassini-like) identity
`A (n-1) * B n - B (n-1) * A n = (-1)^n` for a *simple* continued fraction such as
`GenContFract.of v`: any common divisor of `A n` and `B n` divides `±1`. -/
theorem cf_num_den_coprime (v : ℝ) (hv : ∀ n, ¬ (GenContFract.of v).TerminatedAt n)
    (A : ℕ → ℤ) (B : ℕ → ℕ)
    (hA : ∀ n, (GenContFract.of v).nums n = (A n : ℝ))
    (hB : ∀ n, (GenContFract.of v).dens n = (B n : ℝ)) :
    ∀ n, Nat.Coprime (Int.natAbs (A n)) (B n) := by
  intro n
  rcases n with _ | n
  · -- index `0`: `dens 0 = 1`, so `B 0 = 1`
    have h : (GenContFract.of v).dens 0 = (1 : ℝ) := by simp
    have h' := hB 0
    rw [h'] at h
    have hB0 : B 0 = 1 := by exact_mod_cast h
    rw [hB0]
    exact Nat.coprime_one_right _
  · -- index `n + 1`: apply the determinant identity at index `n`
    have hdet := SimpContFract.determinant (s := SimpContFract.of v) (n := n) (hv n)
    simp only [SimpContFract.of, hA n, hA (n + 1), hB n, hB (n + 1)] at hdet
    have hdetZ : A n * (B (n + 1) : ℤ) - (B n : ℤ) * A (n + 1) = (-1 : ℤ) ^ (n + 1) := by
      exact_mod_cast hdet
    -- any common divisor `d` of `A (n+1)` and `B (n+1)` divides `±1`
    set d := (A (n + 1)).natAbs.gcd (B (n + 1)) with hd
    have key : (d : ℤ) = Int.gcd (A (n + 1)) ((B (n + 1) : ℕ) : ℤ) := by
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    have hdiv1 : (d : ℤ) ∣ A (n + 1) := by
      rw [key]; exact Int.gcd_dvd_left _ _
    have hdiv2 : (d : ℤ) ∣ ((B (n + 1) : ℕ) : ℤ) := by
      rw [key]; exact Int.gcd_dvd_right _ _
    have hdiff : (d : ℤ) ∣ (-1 : ℤ) ^ (n + 1) := by
      rw [← hdetZ]
      exact dvd_sub (dvd_mul_of_dvd_right hdiv2 (A n))
        (dvd_mul_of_dvd_right hdiv1 ((B n : ℕ) : ℤ))
    have hu : ((-1 : ℤ) ^ (n + 1)) ∣ 1 := by
      rcases Nat.even_or_odd (n + 1) with he | ho
      · rw [Even.neg_one_pow he]
      · rw [Odd.neg_one_pow ho]
        exact ⟨-1, by ring⟩
    have hdvd1 : (d : ℤ) ∣ 1 := dvd_trans hdiff hu
    have hd1 : d ∣ 1 := Int.natCast_dvd_natCast.mp hdvd1
    show d = 1
    exact Nat.dvd_one.mp hd1

end Work.TMComp.RedC7T
