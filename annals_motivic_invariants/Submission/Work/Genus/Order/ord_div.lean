import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Order

open Polynomial GCDMonoid

/-- Multiplying by a non-zero constant polynomial does not change the multiplicity of an
irreducible `π`: `F[X]` is a field, so `C c` (`c ≠ 0`) is a unit, and a unit contributes `0`.
(Stated for `ℕ`-valued `multiplicity`; the finiteness instance is supplied by `π` being a non-unit
and the product being non-zero.) -/
theorem multiplicity_C_mul {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π) {c : F}
    (hc : c ≠ 0) (r : Polynomial F) :
    multiplicity π (Polynomial.C c * r) = multiplicity π r := by
  by_cases hr : r = 0
  · simp [hr]
  · rw [multiplicity_mul hπ.prime (FiniteMultiplicity.of_not_isUnit hπ.not_isUnit
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hr)),
      multiplicity_of_isUnit_right (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)), zero_add]

/-- The order of vanishing `Work.Genus.ord π f` of a rational function at the place of an
irreducible `π` (defined as `multiplicity π f.num - multiplicity π f.denom`), computed on an
explicit fraction `p / q`.  Route: `RatFunc.num_div`/`denom_div` write `num (p/q)` and `denom (p/q)`
as a common unit times `p / gcd p q` resp. `q / gcd p q`, and `multiplicity_mul` (with `Prime π`,
from `Irreducible.prime`) is additive on products. -/
theorem ord_div {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π) {p q : Polynomial F}
    (hp : p ≠ 0) (hq : q ≠ 0) :
    Work.Genus.ord π (algebraMap (Polynomial F) (RatFunc F) p / algebraMap (Polynomial F) (RatFunc F) q)
      = (multiplicity π p : ℤ) - (multiplicity π q : ℤ) := by
  classical
  have hgne : gcd p q ≠ 0 := by
    rintro h0
    obtain ⟨c, hc⟩ := gcd_dvd_left p q
    rw [h0, zero_mul] at hc
    exact hp hc
  have hgp : gcd p q * (p / gcd p q) = p := EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left p q)
  have hgq : gcd p q * (q / gcd p q) = q := EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_right p q)
  have hcne : (q / gcd p q).leadingCoeff⁻¹ ≠ 0 :=
    inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (right_div_gcd_ne_zero hq))
  rw [Work.Genus.ord, RatFunc.num_div p q, RatFunc.denom_div p hq,
    multiplicity_C_mul hπ hcne (p / gcd p q), multiplicity_C_mul hπ hcne (q / gcd p q)]
  have hmp : multiplicity π p = multiplicity π (gcd p q) + multiplicity π (p / gcd p q) := by
    conv_lhs => rw [← hgp]
    exact multiplicity_mul hπ.prime
      (FiniteMultiplicity.of_not_isUnit hπ.not_isUnit (by rw [hgp]; exact hp))
  have hmq : multiplicity π q = multiplicity π (gcd p q) + multiplicity π (q / gcd p q) := by
    conv_lhs => rw [← hgq]
    exact multiplicity_mul hπ.prime
      (FiniteMultiplicity.of_not_isUnit hπ.not_isUnit (by rw [hgq]; exact hq))
  have hmpz : (multiplicity π (p / gcd p q) : ℤ)
      = (multiplicity π p : ℤ) - (multiplicity π (gcd p q) : ℤ) := by omega
  have hmqz : (multiplicity π (q / gcd p q) : ℤ)
      = (multiplicity π q : ℤ) - (multiplicity π (gcd p q) : ℤ) := by omega
  rw [hmpz, hmqz]
  first | refl_ring1 | ring

end Work.Genus.Order
