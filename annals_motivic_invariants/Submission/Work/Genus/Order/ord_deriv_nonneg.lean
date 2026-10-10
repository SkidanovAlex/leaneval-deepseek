import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_div
import Submission.Work.Genus.Order.ord_pow

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Order

open Polynomial

/-- **The derivative of a function with no pole at a place has no pole there.**  `ord π f ≥ 0`
implies `ord π (deriv f) ≥ 0`.  Route: `ord π f ≥ 0` forces `multiplicity π f.denom = 0` (by
coprimality of `f.num`, `f.denom`), hence `ord π (deriv f) = multiplicity π A - 2 * 0 ≥ 0` with
`A = f.num.derivative * f.denom - f.num * f.denom.derivative`.  (It also follows from
`ord_deriv_ge` plus `1 ≤ ord π f`; both arguments are fine.) -/
theorem ord_deriv_nonneg {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π)
    {f : RatFunc F} (hf : f ≠ 0) (hf' : Work.Genus.deriv f ≠ 0) (h : 0 ≤ Work.Genus.ord π f) :
    0 ≤ Work.Genus.ord π (Work.Genus.deriv f) := by
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hcop : IsCoprime f.num f.denom := RatFunc.isCoprime_num_denom f
  -- the numerator of `deriv f` as an explicit fraction, before any gcd cancellation
  set A : Polynomial F := f.num.derivative * f.denom - f.num * f.denom.derivative with hAdef
  -- `deriv f` written as the explicit fraction `A / f.denom ^ 2`
  have hderiv_frac : Work.Genus.deriv f
      = algebraMap (Polynomial F) (RatFunc F) A
        / algebraMap (Polynomial F) (RatFunc F) (f.denom ^ 2) := by
    rw [Work.Genus.deriv]
    congr 1
    · simp only [hAdef, map_sub, map_mul]
    · rw [map_pow]
  -- `A ≠ 0`, since otherwise `deriv f = 0`
  have hAne : A ≠ 0 := by
    intro hA0
    exact hf' (by rw [hderiv_frac, hA0, map_zero, zero_div])
  -- `ord π f ≥ 0` forces `π ∤ f.denom`
  have hmultden : multiplicity π f.denom = 0 := by
    by_contra hne
    have hm1 : 1 ≤ multiplicity π f.denom := Nat.one_le_iff_ne_zero.mpr hne
    have hdvd_den : π ∣ f.denom := by
      simpa using pow_dvd_of_le_multiplicity (k := 1) hm1
    have hmn : (multiplicity π f.denom : ℤ) ≤ (multiplicity π f.num : ℤ) := by
      have := h
      rw [Work.Genus.ord] at this
      linarith
    have hn1 : 1 ≤ multiplicity π f.num := by
      have h1 : (1 : ℤ) ≤ (multiplicity π f.denom : ℤ) := by exact_mod_cast hm1
      have : (1 : ℤ) ≤ (multiplicity π f.num : ℤ) := by linarith
      exact_mod_cast this
    have hdvd_num : π ∣ f.num := by
      simpa using pow_dvd_of_le_multiplicity (k := 1) hn1
    exact hπ.not_isUnit (hcop.isUnit_of_dvd' hdvd_num hdvd_den)
  -- evaluate `ord` on the explicit fraction `A / f.denom ^ 2`
  have hq2 : f.denom ^ 2 ≠ 0 := pow_ne_zero 2 hden
  have hord : Work.Genus.ord π (Work.Genus.deriv f)
      = (multiplicity π A : ℤ) - (multiplicity π (f.denom ^ 2) : ℤ) := by
    rw [hderiv_frac]
    exact Work.Genus.Order.ord_div hπ hAne hq2
  have hpow : multiplicity π (f.denom ^ 2) = 2 * multiplicity π f.denom :=
    Work.Genus.Order.multiplicity_pow_of_irreducible hπ hden 2
  rw [hord, hpow, hmultden]
  simp

end Work.Genus.Order
