import Mathlib
import Submission.Work.FIArea4.SqfreeKernel
import Submission.Work.FIArea4.sqfree_kernel

namespace Work.FIArea7

/-- For `n ≠ 0` and a prime `p`, the exponent of `p` in `n` is odd exactly when `p` divides the
squarefree kernel of `n`.

Proof: `Work.FIArea4.sqfree_kernel n hn` gives `K * s ^ 2 = n` with `K = sqfreeKernel n`
squarefree and `s = sqPart n`.  From `Nat.factorization_mul` and `Nat.factorization_pow`
one gets, at `p`, `n.factorization p = K.factorization p + 2 * s.factorization p`
(a `Finsupp` identity, `2 • s.factorization`, usable pointwise).  Squarefreeness
(`Nat.squarefree_iff_factorization_le_one`) gives `K.factorization p ≤ 1`, hence
`K.factorization p ∈ {0,1}`, so `p ∣ K ↔ K.factorization p = 1 ↔ Odd (n.factorization p)`:
the leftmost equivalence uses `Nat.factorization_eq_zero_iff` (with `p` prime, `K ≠ 0`, the latter
from `K * s ^ 2 = n ≠ 0`) and the rightmost that adding `2 * k` does not change parity
(`Nat.even_two_mul`, `Nat.odd_iff`, `Nat.even_add`). -/
theorem sqfreeKernel_dvd_iff_odd (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) :
    p ∣ Work.FIArea4.sqfreeKernel n ↔ Odd (n.factorization p) := by
  obtain ⟨hP, hmax, hsqm, hdvdk, hsf⟩ := Work.FIArea4.sqfree_kernel n hn
  set K := Work.FIArea4.sqfreeKernel n
  set s := Work.FIArea4.sqPart n
  have hs1 : 1 ≤ s := hmax 1 (by simp)
  have hs0 : s ≠ 0 := by omega
  have hs2ne : s ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  -- `K ≠ 0` because `K * s ^ 2 = n ≠ 0`.
  have hK0 : K ≠ 0 := by
    intro h
    rw [h] at hsqm
    simp at hsqm
    exact hn hsqm.symm
  -- Squarefreeness of `K` bounds its factorization exponent at `p` by `1`.
  have hle1 : K.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hK0).mp hsf p
  -- The exponent identity `n.factorization p = K.factorization p + 2 * s.factorization p`.
  have key : n.factorization p = K.factorization p + 2 * s.factorization p := by
    conv_lhs => rw [← hsqm]
    rw [Nat.factorization_mul hK0 hs2ne, Nat.factorization_pow]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, smul_eq_mul]
  -- Adding the even number `2 * s.factorization p` does not change parity.
  have hpar : Odd (n.factorization p) ↔ Odd (K.factorization p) := by
    rw [key, Nat.odd_add]
    simp
  rw [hp.dvd_iff_one_le_factorization hK0, hpar]
  have hcases : K.factorization p = 0 ∨ K.factorization p = 1 := by omega
  rcases hcases with h | h <;> simp [h]

end Work.FIArea7
