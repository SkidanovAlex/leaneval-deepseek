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

open Polynomial

/-- Additivity of `Polynomial.multiplicity` with values pushed to `ℤ`: for a prime (e.g. an
irreducible) modulus `π` and non-zero factors `a`, `b`, the multiplicity of `π` in the product is
the sum of the multiplicities.  Finiteness of the multiplicities comes from `π` being a non-unit
and `a`, `b` being non-zero in the `WfDvdMonoid` `F[X]`. -/
theorem multiplicity_mul_int {F : Type*} [Field F] {π : Polynomial F} (hπ : Prime π)
    {a b : Polynomial F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (multiplicity π (a * b) : ℤ) = (multiplicity π a : ℤ) + (multiplicity π b : ℤ) := by
  have hfa : FiniteMultiplicity π a := FiniteMultiplicity.of_prime_left hπ ha
  have hfb : FiniteMultiplicity π b := FiniteMultiplicity.of_prime_left hπ hb
  have h := multiplicity_mul hπ (hπ.finiteMultiplicity_mul hfa hfb)
  rw [h]
  push_cast
  first | refl_ring1 | ring

/-- The order of vanishing at the place of an irreducible `π` is additive on products.
Route: `RatFunc.num_denom_mul` and `multiplicity_mul` (`Prime π` from `Irreducible.prime`); the
finiteness instances come from `p ≠ 0` and `π` non-constant. -/
theorem ord_mul {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π) {f g : RatFunc F}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    Work.Genus.ord π (f * g) = Work.Genus.ord π f + Work.Genus.ord π g := by
  have hp : Prime π := hπ.prime
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hnum_fg : (f * g).num ≠ 0 := RatFunc.num_ne_zero hfg
  have hden_fg : (f * g).denom ≠ 0 := RatFunc.denom_ne_zero _
  have hnum_f : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hnum_g : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hden_f : f.denom ≠ 0 := RatFunc.denom_ne_zero _
  have hden_g : g.denom ≠ 0 := RatFunc.denom_ne_zero _
  -- `num_denom_mul` is the identity `(f * g).num * (f.denom * g.denom) = f.num * g.num * (f * g).denom`
  -- in the fraction field, valid without any coprimality assumption.
  have key := congrArg (fun p : Polynomial F => (multiplicity π p : ℤ))
    (RatFunc.num_denom_mul f g)
  rw [multiplicity_mul_int hp hnum_fg (mul_ne_zero hden_f hden_g),
    multiplicity_mul_int hp hden_f hden_g,
    multiplicity_mul_int hp (mul_ne_zero hnum_f hnum_g) hden_fg,
    multiplicity_mul_int hp hnum_f hnum_g] at key
  simp only [Work.Genus.ord]
  linarith

end Work.Genus.Order
