import Mathlib
import Submission.Work.FIArea7.oddPartKernelDefs

namespace Work.FIArea7

/-- The odd part `n / 2 ^ (n.factorization 2)` of a nonzero number is nonzero. -/
private lemma oddPart_ne_zero' {n : ℕ} (hn : n ≠ 0) : Work.FIPlan.oddPart n ≠ 0 := by
  intro h
  have h' : n / 2 ^ n.factorization 2 * 2 ^ n.factorization 2 = n :=
    Nat.div_mul_cancel (Nat.ordProj_dvd n 2)
  rw [Work.FIPlan.oddPart] at h
  rw [h, zero_mul] at h'
  exact hn h'.symm

/-- The odd part `n / 2 ^ (n.factorization 2)` of a nonzero number is odd. -/
private lemma oddPart_odd' {n : ℕ} (hn : n ≠ 0) : Odd (Work.FIPlan.oddPart n) := by
  rw [← Nat.not_even_iff_odd]
  intro hE
  exact Nat.not_dvd_ordCompl Nat.prime_two hn (even_iff_two_dvd.mp hE)

-- Hint: `Kern n = sqfreeKernel (oddPart n)` and `oddPart n = n / 2^(n.factorization 2)`, and
-- `Work.FIArea4.sqfree_kernel` gives, for `m ≠ 0`, `sqfreeKernel m * sqPart m ^ 2 = m`.
-- Take `s := Work.FIArea4.sqPart (Work.FIPlan.oddPart n)` and `j := n.factorization 2`; then
-- `h : Kern n = d` turns that identity into `d * s ^ 2 = oddPart n`, and `s` is odd because
-- `s ^ 2 ∣ oddPart n` and `oddPart n` is odd.  Finally `oddPart n * 2 ^ (n.factorization 2) = n`.
/-- **Decomposition of a number along its kernel.**  For `n > 0`, writing `d = Kern n` for the
squarefree kernel of the odd part of `n`, there are `s, j` with `s` odd and `d * s ^ 2 * 2 ^ j = n`
(namely `s = sqPart (oddPart n)`, the largest `s` with `s ^ 2 ∣ oddPart n`, and
`j = n.factorization 2`, the exponent of `2` in `n`). -/
theorem Kern_decomp (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (h : Work.FIArea7.Kern n = d) :
    ∃ s j : ℕ, Odd s ∧ d * s ^ 2 * 2 ^ j = n := by
  have hn0 : n ≠ 0 := hn.ne'
  have hm : Work.FIPlan.oddPart n ≠ 0 := oddPart_ne_zero' hn0
  obtain ⟨hP, -, hsq, -, -⟩ := Work.FIArea4.sqfree_kernel (Work.FIPlan.oddPart n) hm
  -- `oddPart n * 2 ^ (n.factorization 2) = n`
  have hnm : Work.FIPlan.oddPart n * 2 ^ (n.factorization 2) = n := by
    rw [Work.FIPlan.oddPart]
    exact Nat.div_mul_cancel (Nat.ordProj_dvd n 2)
  refine ⟨Work.FIArea4.sqPart (Work.FIPlan.oddPart n), n.factorization 2, ?_, ?_⟩
  · -- `sqPart (oddPart n)` is odd: its square divides the odd number `oddPart n`.
    rw [← Nat.not_even_iff_odd]
    intro hs
    have h2s : 2 ∣ Work.FIArea4.sqPart (Work.FIPlan.oddPart n) := even_iff_two_dvd.mp hs
    have h2sq : 2 ∣ Work.FIArea4.sqPart (Work.FIPlan.oddPart n) ^ 2 := by
      rw [pow_two]
      exact dvd_mul_of_dvd_left h2s _
    exact (oddPart_odd' hn0).not_two_dvd_nat (dvd_trans h2sq hP)
  · -- `sqfreeKernel (oddPart n) * sqPart (oddPart n) ^ 2 = oddPart n`, then `* 2 ^ ν = n`.
    rw [← h, Kern, hsq, hnm]

end Work.FIArea7
