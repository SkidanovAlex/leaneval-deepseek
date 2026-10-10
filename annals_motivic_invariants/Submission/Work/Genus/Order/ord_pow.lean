import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Order


/-- **The numerator and denominator of a power, cross-multiplied.** For `f : 𝔽(t)` and `n : ℕ`,
`(f ^ n).num * f.denom ^ n = f.num ^ n * (f ^ n).denom`, i.e. writing `f ^ n` in reduced form
introduces no factor beyond those already present in `f.num ^ n` and `f.denom ^ n`.  This is the
form of the reduced-form statement that is stable under `multiplicity` (no gcd cancellation
needed): it follows from `RatFunc.num_div_denom` for `f ^ n` combined with
`f ^ n = (f.num / f.denom) ^ n`. -/
theorem num_denom_pow {F : Type*} [Field F] (f : RatFunc F) (n : ℕ) :
    (f ^ n).num * f.denom ^ n = f.num ^ n * (f ^ n).denom := by
  have h : f ^ n = algebraMap (Polynomial F) (RatFunc F) (f.num ^ n)
      / algebraMap (Polynomial F) (RatFunc F) (f.denom ^ n) := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [div_pow, ← map_pow, ← map_pow]
  exact (RatFunc.num_mul_eq_mul_denom_iff (pow_ne_zero n (RatFunc.denom_ne_zero f))).mpr h

/-- **Multiplicativity of `multiplicity` under powers.** For an irreducible `π` (which is prime in
`𝔽[X]`) and `p ≠ 0`, the multiplicity of `π` in `p ^ n` is `n` times its multiplicity in `p`.
The finiteness of the multiplicity comes from `FiniteMultiplicity.of_prime_left` (`𝔽[X]` is a
`WfDvdMonoid`). -/
theorem multiplicity_pow_of_irreducible {F : Type*} [Field F] {π p : Polynomial F}
    (hπ : Irreducible π) (hp : p ≠ 0) (n : ℕ) :
    multiplicity π (p ^ n) = n * multiplicity π p :=
  (FiniteMultiplicity.of_prime_left hπ.prime hp).multiplicity_pow hπ.prime

/-- The order of vanishing at the place of an irreducible `π` of a power `f ^ n`. -/
theorem ord_pow {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π) {f : RatFunc F}
    (hf : f ≠ 0) (n : ℕ) : Work.Genus.ord π (f ^ n) = n * Work.Genus.ord π f := by
  rw [Work.Genus.ord, Work.Genus.ord]
  have hfn : f ^ n ≠ 0 := pow_ne_zero n hf
  -- both sides of the cross-multiplied identity have finite `π`-multiplicity
  have hfinL : FiniteMultiplicity π ((f ^ n).num * f.denom ^ n) :=
    FiniteMultiplicity.of_prime_left hπ.prime
      (mul_ne_zero (RatFunc.num_ne_zero hfn) (pow_ne_zero n (RatFunc.denom_ne_zero f)))
  have hfinR : FiniteMultiplicity π (f.num ^ n * (f ^ n).denom) :=
    FiniteMultiplicity.of_prime_left hπ.prime
      (mul_ne_zero (pow_ne_zero n (RatFunc.num_ne_zero hf)) (RatFunc.denom_ne_zero (f ^ n)))
  -- the `ℕ`-valued multiplicities of the two sides
  have hL : multiplicity π ((f ^ n).num * f.denom ^ n)
      = multiplicity π (f ^ n).num + n * multiplicity π f.denom := by
    rw [multiplicity_mul hπ.prime hfinL, multiplicity_pow_of_irreducible hπ (RatFunc.denom_ne_zero f) n]
  have hR : multiplicity π (f.num ^ n * (f ^ n).denom)
      = n * multiplicity π f.num + multiplicity π (f ^ n).denom := by
    rw [multiplicity_mul hπ.prime hfinR, multiplicity_pow_of_irreducible hπ (RatFunc.num_ne_zero hf) n]
  -- comparing them through the polynomial identity `num_denom_pow` gives a relation in `ℕ`
  have hNat : multiplicity π (f ^ n).num + n * multiplicity π f.denom
      = n * multiplicity π f.num + multiplicity π (f ^ n).denom := by
    rw [← hL, ← hR, num_denom_pow f n]
  -- which immediately yields the `ℤ`-valued statement for `ord`
  have hcast := congrArg (fun m : ℕ => (m : ℤ)) hNat
  push_cast at hcast
  linarith

end Work.Genus.Order
