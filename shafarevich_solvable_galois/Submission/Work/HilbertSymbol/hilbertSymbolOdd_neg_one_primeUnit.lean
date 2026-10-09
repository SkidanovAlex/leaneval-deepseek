import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.legendreOf_intUnit
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_primeUnit_self
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- No prime `p` divides `-1` in `ℤ`. -/
private theorem not_dvd_neg_one {p : ℕ} [Fact p.Prime] : ¬ (p : ℤ) ∣ (-1 : ℤ) := by
  intro hd
  have hd1 : (p : ℤ) ∣ (1 : ℤ) := dvd_neg.mp hd
  have hu : IsUnit (p : ℤ) := isUnit_of_dvd_one hd1
  rcases Int.isUnit_iff.mp hu with h1 | h1
  · exact (Fact.out : p.Prime).ne_one (by exact_mod_cast h1)
  · have : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
    omega

/-- `-1` as a unit of `ℚ` is `intUnit (-1)`. -/
private theorem intUnit_neg_one_eq : intUnit (-1) (by norm_num) = (-1 : ℚˣ) := by
  ext; simp [intUnit, ratUnit]

theorem hilbertSymbolOdd_neg_one_primeUnit {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    hilbertSymbolOdd p (-1 : ℚˣ) (primeUnit p) = intUnitOf (legendreSym p (-1)) := by
  have _ := hp
  have hv : padicVal p (-1 : ℚˣ) = 0 := by rw [padicVal_neg, padicVal_one]
  rw [hilbertSymbolOdd, hv, padicVal_primeUnit, legendreOf_primeUnit]
  simp only [zero_mul, zpow_zero, zpow_one, one_mul, mul_one]
  rw [← intUnit_neg_one_eq,
    legendreOf_intUnit (m := -1) (by norm_num : (-1 : ℤ) ≠ 0) (not_dvd_neg_one (p := p))]

end Work.HilbertSymbol

