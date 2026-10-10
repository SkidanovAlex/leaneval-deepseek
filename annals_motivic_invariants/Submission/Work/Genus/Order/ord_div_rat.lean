import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_div
import Submission.Work.Genus.Order.ord_mul
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Order

/-- The order of vanishing at the place of an irreducible `π` is additive on quotients.

Route: `f / g` is written as the explicit fraction
`algebraMap (f.num * g.denom) / algebraMap (f.denom * g.num)` (via `RatFunc.num_div_denom`);
`ord_div` evaluates `ord π` on an explicit fraction as `multiplicity π` of numerator minus
`multiplicity π` of denominator, and `multiplicity_mul_int` (a `Prime π` from `Irreducible π`)
splits the products.  The two sides then differ by `ring` in `ℤ`. -/
theorem ord_div_rat {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π) {f g : RatFunc F}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    Work.Genus.ord π (f / g) = Work.Genus.ord π f - Work.Genus.ord π g := by
  have hfnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hfden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hgnum : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hgden : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  -- `f / g = (f.num * g.denom) / (f.denom * g.num)`, as an explicit fraction of polynomials.
  have hkey : algebraMap (Polynomial F) (RatFunc F) (f.num * g.denom)
      / algebraMap (Polynomial F) (RatFunc F) (f.denom * g.num) = f / g := by
    have hD : (algebraMap (Polynomial F) (RatFunc F)) g.denom
        / (algebraMap (Polynomial F) (RatFunc F)) g.num = g⁻¹ := by
      rw [← inv_div, RatFunc.num_div_denom g]
    rw [map_mul, map_mul, ← div_mul_div_comm, RatFunc.num_div_denom f, hD, div_eq_mul_inv]
  rw [← hkey, ord_div hπ (mul_ne_zero hfnum hgden) (mul_ne_zero hfden hgnum),
    multiplicity_mul_int hπ.prime hfnum hgden, multiplicity_mul_int hπ.prime hfden hgnum]
  simp only [Work.Genus.ord]
  first | refl_ring1 | ring

end Work.Genus.Order
