import Mathlib
import Submission.Work.DSTR.M110.padicValNatPowAddOne

namespace Work.DSTR.M110

/-- LTE (Lifting The Exponent), `factorization` form: for an odd prime `q` dividing `A + 1`,
the `q`-adic exponent of `A ^ q + 1` exceeds that of `A + 1` by exactly one.

Immediate from the `padicValNat` version `padicValNatPowAddOne` via the identification of
`n.factorization q` with `padicValNat q n` for a prime `q`. -/
theorem powAddOneFactorizationOfDvd (A q : ℕ) (hq : q.Prime) (hqo : Odd q) (hdvd : q ∣ A + 1) : (A ^ q + 1).factorization q = (A + 1).factorization q + 1 := by
  rw [Nat.factorization_def (A ^ q + 1) hq, Nat.factorization_def (A + 1) hq]
  exact padicValNatPowAddOne A q hq hqo hdvd

end Work.DSTR.M110
