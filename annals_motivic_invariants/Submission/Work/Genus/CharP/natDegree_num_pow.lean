import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.CharP

open Polynomial

/-- **Uniqueness of the reduced form of a rational function.**
If `x : RatFunc F` admits a presentation `x = a / b` with `a ≠ 0`, `b ≠ 0`, `a` and `b` coprime
and `b` monic, then this presentation is already the normalized one: `x.num = a` and
`x.denom = b`.

Both `a` and `b` are multiples of `x.num` resp. `x.denom` (`RatFunc.num_dvd`, `RatFunc.denom_dvd`),
say `a = x.num * s` and `b = x.denom * t`, and `x.num * b = a * x.denom`
(`RatFunc.num_mul_eq_mul_denom_iff`) forces `s = t`. Then `s` divides both `a` and `b`, so
coprimality makes it a unit (`IsCoprime.isUnit_of_dvd'`), and `b = x.denom * s` with `b` and
`x.denom` monic makes `s` monic, hence `s = 1`. -/
lemma num_denom_eq_of_eq_div {F : Type*} [Field F] {x : RatFunc F} {a b : F[X]}
    (ha : a ≠ 0) (hb : b ≠ 0) (hcop : IsCoprime a b) (hmon : b.Monic)
    (hx : x = algebraMap F[X] (RatFunc F) a / algebraMap F[X] (RatFunc F) b) :
    x.num = a ∧ x.denom = b := by
  have hx0 : x ≠ 0 := by
    rw [hx]
    exact div_ne_zero (RatFunc.algebraMap_ne_zero ha) (RatFunc.algebraMap_ne_zero hb)
  have hnum : x.num ≠ 0 := RatFunc.num_ne_zero hx0
  have hden : x.denom ≠ 0 := RatFunc.denom_ne_zero x
  have h1 : x.num * b = a * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hb).mpr hx
  obtain ⟨s, hs⟩ : ∃ s, a = x.num * s := (RatFunc.num_dvd ha).mpr ⟨b, hb, hx⟩
  obtain ⟨t, ht⟩ : ∃ t, b = x.denom * t := (RatFunc.denom_dvd hb).mpr ⟨a, hx⟩
  have h2 : s = t := by
    have key : x.num * (x.denom * t) = x.num * (s * x.denom) := by
      calc x.num * (x.denom * t) = x.num * b := by rw [ht]
        _ = a * x.denom := h1
        _ = x.num * (s * x.denom) := by rw [hs, mul_assoc]
    have key2 : x.denom * t = s * x.denom := mul_left_cancel₀ hnum key
    rw [mul_comm s] at key2
    exact (mul_left_cancel₀ hden key2).symm
  have hunit : IsUnit s :=
    hcop.isUnit_of_dvd' ⟨x.num, by rw [hs, mul_comm]⟩ ⟨x.denom, by rw [ht, ← h2, mul_comm]⟩
  have hmon_s : s.Monic :=
    (RatFunc.monic_denom x).of_mul_monic_left (by rw [h2, ← ht]; exact hmon)
  have hs1 : s = 1 := hmon_s.eq_one_of_isUnit hunit
  exact ⟨by rw [hs, hs1, mul_one], by rw [ht, ← h2, hs1, mul_one]⟩

/-- The degree of the numerator of a power.  Route: for `f ≠ 0` the reduced form of `f ^ n` is
`(f.num) ^ n / (f.denom) ^ n` (coprimality is preserved by powers and `f.denom` is monic), so
`(f ^ n).num = (f.num) ^ n` and `Polynomial.natDegree_pow` applies.  Use `RatFunc.num_div`,
`RatFunc.isCoprime_num_denom` and the second component of `RatFunc.num_denom` (or `num_denom_mul`
inductively). -/
theorem natDegree_num_pow {F : Type*} [Field F] {f : RatFunc F} (hf : f ≠ 0) (n : ℕ) :
    (f ^ n).num.natDegree = n * f.num.natDegree := by
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have key : (f ^ n).num = f.num ^ n := by
    have hx : f ^ n = algebraMap F[X] (RatFunc F) (f.num ^ n)
        / algebraMap F[X] (RatFunc F) (f.denom ^ n) := by
      conv_lhs => rw [← RatFunc.num_div_denom f]
      rw [div_pow, ← map_pow, ← map_pow]
    exact (num_denom_eq_of_eq_div (pow_ne_zero n hnum) (pow_ne_zero n hden)
      (RatFunc.isCoprime_num_denom f).pow ((RatFunc.monic_denom f).pow n) hx).1
  rw [key, Polynomial.natDegree_pow]

end Work.Genus.CharP
