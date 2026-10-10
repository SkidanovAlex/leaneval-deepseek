import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Deriv.Defs
import Submission.Work.Genus.Deriv.derivQuot_congr
import Submission.Work.Genus.Deriv.derivQuot_mul

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Deriv

/-- The Leibniz rule for the formal derivative `Work.Genus.deriv` on `F(t)`.  (As in `deriv_add`,
the quotient-rule expression is independent of the chosen representation `f = p/q`; write both sides
over the common denominator `q² s²` and expand with the Leibniz rule for `Polynomial.derivative`.) -/
theorem deriv_mul {F : Type*} [Field F] (f g : RatFunc F) :
    Work.Genus.deriv (f * g) = Work.Genus.deriv f * g + f * Work.Genus.deriv g := by
  -- `RatFunc.num_denom_mul` exhibits the canonical representation of `f * g` as a common multiple
  -- of the product representation `(f.num * g.num) / (f.denom * g.denom)`, on which the
  -- quotient-rule expression is defined independently of the representation (`derivQuot_congr`).
  have hcongr : derivQuot (f * g).num (f * g).denom
      = derivQuot (f.num * g.num) (f.denom * g.denom) :=
    derivQuot_congr (RatFunc.num_denom_mul f g) (RatFunc.denom_ne_zero _)
      (mul_ne_zero (RatFunc.denom_ne_zero _) (RatFunc.denom_ne_zero _))
  -- `deriv` *is* the quotient-rule expression on the canonical representation (`deriv_eq_derivQuot`),
  -- and `f = f.num / f.denom`, `g = g.num / g.denom` (`RatFunc.num_div_denom`)
  show derivQuot (f * g).num (f * g).denom
      = derivQuot f.num f.denom * g + f * derivQuot g.num g.denom
  rw [hcongr, derivQuot_mul (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g),
      RatFunc.num_div_denom g, RatFunc.num_div_denom f]

end Work.Genus.Deriv
