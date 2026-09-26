import Mathlib
import Submission.Work.PTCert.GlueDefs

/-!
# `chiSTwo`: the `m = 2` sign-character table

Both sides are the sign `(-1)^(popcount (b &&& psi))`: `chiS (maskSet psi) (zOfSc b)` is the
product over the two bits `i ∈ {0,1}` with `psi`-bit set of `(if b-bit = 0 then 1 else -1)`,
and the exponent `(b &&& psi) % 2 + ((b &&& psi) / 2) % 2` is the parity of the number of set
bits of `b &&& psi`.  With `psi, b < 4` there are 16 cases, closed by evaluation.
-/

namespace Work.PTCert

theorem chiSTwo (psi b : ℕ) (hp : psi < 4) (hb : b < 4) :
    Submission.PTCert.chiS (Submission.PTCert.maskSet (m := 2) psi) (Submission.PTCert.zOfSc (m := 2) b)
      = (if ((b &&& psi) % 2 + ((b &&& psi) / 2) % 2) = 1 then (-1 : ℝ) else 1) := by
  interval_cases psi <;> interval_cases b <;>
    rw [Submission.PTCert.chiS, Submission.PTCert.maskSet, Finset.prod_filter, Fin.prod_univ_two] <;>
    simp only [Submission.PTCert.zOfSc, Submission.PTCert.sbit, Nat.shiftRight_eq_div_pow] <;>
    norm_num <;> decide

end Work.PTCert
