import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_mul
import Submission.Work.Genus.Order.min_ord_le_ord_add
import Submission.Work.Genus.Order.ord_div
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

/-- The strict non-archimedean equality at the place of an irreducible `π`: if the two orders
differ, the order of the sum is the smaller order.  (The case `f + g = 0` is impossible under the
hypothesis, since `ord π (-f) = ord π f`.) -/
theorem ord_add_eq_of_lt {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π)
    {f g : RatFunc F} (hf : f ≠ 0) (h : Work.Genus.ord π f < Work.Genus.ord π g) :
    Work.Genus.ord π (f + g) = Work.Genus.ord π f := by
  classical
  by_cases hg : g = 0
  · simp [hg]
  have hp : Prime π := hπ.prime
  have hnum_f : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden_f : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hnum_g : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hden_g : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hq : f.denom * g.denom ≠ 0 := mul_ne_zero hden_f hden_g
  -- The strict inequality, read through the `π`-multiplicities of numerator and denominator.
  have key : (multiplicity π f.num : ℤ) + (multiplicity π g.denom : ℤ)
      < (multiplicity π g.num : ℤ) + (multiplicity π f.denom : ℤ) := by
    have h' := h
    simp only [Work.Genus.ord] at h'
    linarith
  -- The corresponding strict inequality of multiplicities of the two polynomial summands.
  have hlt : multiplicity π (f.num * g.denom) < multiplicity π (f.denom * g.num) := by
    rw [multiplicity_mul hp (hp.finiteMultiplicity_mul
          (FiniteMultiplicity.of_prime_left hp hnum_f)
          (FiniteMultiplicity.of_prime_left hp hden_g)),
        multiplicity_mul hp (hp.finiteMultiplicity_mul
          (FiniteMultiplicity.of_prime_left hp hden_f)
          (FiniteMultiplicity.of_prime_left hp hnum_g))]
    have key' : (multiplicity π f.num : ℤ) + (multiplicity π g.denom : ℤ)
        < (multiplicity π f.denom : ℤ) + (multiplicity π g.num : ℤ) := by linarith
    exact_mod_cast key'
  -- The common numerator is non-zero: otherwise the two summands would be opposite, contradicting
  -- the strict inequality above.
  have hpne : f.num * g.denom + f.denom * g.num ≠ 0 := by
    intro h0
    have hswap : f.num * g.denom = -(f.denom * g.num) := eq_neg_of_add_eq_zero_left h0
    have heq : multiplicity π (f.num * g.denom) = multiplicity π (f.denom * g.num) := by
      rw [hswap, multiplicity_neg]
    exact absurd heq (ne_of_lt hlt)
  -- `f + g` written as the explicit fraction `p / q`.
  have hfrac : f + g =
      algebraMap (Polynomial F) (RatFunc F) (f.num * g.denom + f.denom * g.num)
        / algebraMap (Polynomial F) (RatFunc F) (f.denom * g.denom) :=
    (RatFunc.num_mul_eq_mul_denom_iff hq).mp (RatFunc.num_denom_add f g)
  have hord : Work.Genus.ord π (f + g)
      = (multiplicity π (f.num * g.denom + f.denom * g.num) : ℤ)
        - (multiplicity π f.denom : ℤ) - (multiplicity π g.denom : ℤ) := by
    rw [hfrac, ord_div hπ hpne hq, multiplicity_mul_int hπ.prime hden_f hden_g]
    first | refl_ring1 | ring
  -- The multiplicity of `π` in the numerator is that of the smaller summand.
  have hpmult : (multiplicity π (f.num * g.denom + f.denom * g.num) : ℤ)
      = (multiplicity π f.num : ℤ) + (multiplicity π g.denom : ℤ) := by
    have hb : f.num * g.denom + f.denom * g.num = f.denom * g.num + f.num * g.denom := by ring
    have hfin_b : FiniteMultiplicity π (f.num * g.denom) :=
      FiniteMultiplicity.of_not_isUnit hπ.not_isUnit (mul_ne_zero hnum_f hden_g)
    rw [hb, hfin_b.multiplicity_add_of_gt hlt, multiplicity_mul_int hπ.prime hnum_f hden_g]
  rw [hord, hpmult]
  simp only [Work.Genus.ord]
  first | refl_ring1 | ring

end Work.Genus.Order
