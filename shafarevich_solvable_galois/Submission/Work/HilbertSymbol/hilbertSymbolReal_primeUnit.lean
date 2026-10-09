import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

theorem hilbertSymbolReal_primeUnit {p q : ℕ} [Fact p.Prime] [Fact q.Prime] :
    hilbertSymbolReal (primeUnit p) (primeUnit q) = 1 := by
  rw [hilbertSymbolReal_eq_one_iff]
  rintro ⟨h1, _⟩
  rw [primeUnit_coe] at h1
  exact absurd h1 (not_lt.mpr (Nat.cast_nonneg p))

end Work.HilbertSymbol
