import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.digitArith
import Submission.Work.PTCert.codeFactsAux.digitsRecon

namespace Work.PTCert.codeFactsAux

/-- Facts about the binary sign code `scOf` and its decoder `scBits`.
`scOf s = ∑ i : Fin 5, (if s i then 1 else 0) * 2 ^ i.val`, `scBits sc i = decide (sbit sc i.val = 1)`,
`sbit sc i = sc >>> i % 2`.
Useful: `Work.PTCert.selfDigits` (n < b^k → n = ∑ i<k (n / b^i % b) * b^i) from digitsRecon,
`Work.PTCert.sbit_eq_div` (sbit sc i = sc / 2^i % 2), `Work.PTCert.digits.sum_mul_pow_div_mod`,
`Work.PTCert.digits.sum_mul_pow_lt_pow`, `Work.PTCert.digitArith` (its second and third conjuncts are
exactly the `s`-indexed version of the first two components here for `r = 5`, and the third here),
`Fin.sum_univ_eq_sum_range`. -/
theorem scFacts :
    (∀ s : Fin 5 → Bool, Submission.PTCert.scBits (Submission.PTCert.scOf s) = s) ∧
    (∀ sc : ℕ, sc < 32 → Submission.PTCert.scOf (Submission.PTCert.scBits sc) = sc) ∧
    (∀ s : Fin 5 → Bool, Submission.PTCert.scOf s < 32) := by
  obtain ⟨_, hbit, hlt⟩ := Work.PTCert.digitArith 5 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · -- `scBits (scOf s) = s`: the bits of the packed code `scOf s` are exactly `s`.
    intro s
    funext i
    change decide
      (Submission.PTCert.sbit
        (∑ t : Fin 5, (if s t = true then 1 else 0) * 2 ^ (t : ℕ)) i.val = 1) = s i
    rw [hbit s i]
    cases s i <;> rfl
  · -- `scOf (scBits sc) = sc` for `sc < 32`: base-2 digit reconstruction.
    intro sc hsc
    have hsc' : sc < 2 ^ 5 := by norm_num at hsc ⊢; exact hsc
    have hsd := Work.PTCert.selfDigits (b := 2) (by norm_num) sc 5 hsc'
    have hstep : Submission.PTCert.scOf (Submission.PTCert.scBits sc) =
        ∑ i : Fin 5, (sc / 2 ^ i.val % 2) * 2 ^ i.val := by
      unfold Submission.PTCert.scOf Submission.PTCert.scBits
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hcore : (if decide (Submission.PTCert.sbit sc i.val = 1) then (1 : ℕ) else 0)
          = sc / 2 ^ i.val % 2 := by
        rw [Work.PTCert.sbit_eq_div]
        rcases (by omega : sc / 2 ^ i.val % 2 = 0 ∨ sc / 2 ^ i.val % 2 = 1) with h | h <;>
          simp [h]
      rw [hcore]
    rw [hstep, Fin.sum_univ_eq_sum_range (fun i => (sc / 2 ^ i % 2) * 2 ^ i) 5]
    exact hsd.symm
  · -- `scOf s < 32`: the packed code fits in 5 bits.
    intro s
    have h := hlt s
    have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
    rw [h32] at h
    simpa [Submission.PTCert.scOf] using h

end Work.PTCert.codeFactsAux
