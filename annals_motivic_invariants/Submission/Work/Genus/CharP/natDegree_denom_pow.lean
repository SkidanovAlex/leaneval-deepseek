import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.NumDenom.num_denom_eq_of_isCoprime

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.CharP

open Polynomial

set_option linter.unusedVariables false in
/-- The degree of the denominator of a power.  Route: the reduced form of `f ^ n` is
`(f.num) ^ n / (f.denom) ^ n`, so `(f ^ n).denom = (f.denom) ^ n` and `Polynomial.natDegree_pow`
applies.  The reduced-form uniqueness is
`Work.Genus.NumDenom.num_denom_eq_of_isCoprime`. -/
theorem natDegree_denom_pow {F : Type*} [Field F] {f : RatFunc F} (hf : f ≠ 0) (n : ℕ) :
    (f ^ n).denom.natDegree = n * f.denom.natDegree := by
  -- `f ^ n = (num f) ^ n / (denom f) ^ n`, a fraction in lowest terms with monic denominator.
  have hQ : f.denom ^ n ≠ 0 := pow_ne_zero n (RatFunc.denom_ne_zero f)
  have hpow : algebraMap F[X] (RatFunc F) (f.num ^ n) /
      algebraMap F[X] (RatFunc F) (f.denom ^ n) = f ^ n := by
    rw [map_pow, map_pow, ← div_pow]
    conv_rhs => rw [← RatFunc.num_div_denom f]
  have hcop : IsCoprime (f.num ^ n) (f.denom ^ n) := (RatFunc.isCoprime_num_denom f).pow
  have hmon : (f.denom ^ n).Monic := (RatFunc.monic_denom f).pow n
  -- so it is the canonical reduced form of `f ^ n`
  obtain ⟨-, hden⟩ := Work.Genus.NumDenom.num_denom_eq_of_isCoprime hQ hcop hmon hpow
  rw [hden, Polynomial.natDegree_pow]

end Work.Genus.CharP
