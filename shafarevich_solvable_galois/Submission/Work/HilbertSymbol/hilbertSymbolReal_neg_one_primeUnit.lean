import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- At the archimedean place, `(-1, p)_∞ = 1` for a prime `p`: the symbol is `-1` exactly when
both arguments are negative, but `(primeUnit p : ℚ) = p > 0`. -/
theorem hilbertSymbolReal_neg_one_primeUnit {p : ℕ} [Fact p.Prime] :
    hilbertSymbolReal (-1 : ℚˣ) (primeUnit p) = 1 := by
  rw [hilbertSymbolReal_eq_one_iff]
  rintro ⟨h1, h2⟩
  rw [primeUnit_coe] at h2
  have hp : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (Fact.out : p.Prime).pos
  linarith

end Work.HilbertSymbol
