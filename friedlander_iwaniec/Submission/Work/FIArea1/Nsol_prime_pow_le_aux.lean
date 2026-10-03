import Mathlib
import Submission.Work.FIArea1.Defs
import Submission.Work.FIArea1.Nsol_prime_pow_le

set_option autoImplicit false

namespace Work.FIArea1

/-- The divisor sum `N(p^e)` of *FI* §5 is at most `(e+1) p^e`; this is the
`aux`-name of `Work.FIArea1.Nsol_prime_pow_le`. -/
theorem Nsol_prime_pow_le_aux {p e : ℕ} (hp : p.Prime) :
    Work.FIArea1.Nsol (p ^ e) ≤ (e + 1) * p ^ e :=
  Nsol_prime_pow_le hp

end Work.FIArea1
