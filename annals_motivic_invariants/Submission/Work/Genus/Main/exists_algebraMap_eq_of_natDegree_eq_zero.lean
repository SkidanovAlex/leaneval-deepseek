import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Main

/-- A rational function whose numerator and denominator are both constant is a constant.  Route:
`RatFunc.denom` is monic, so `denom.natDegree = 0` gives `denom = 1` (`Polynomial.natDegree_eq_zero`),
and then `f = f.num` (`RatFunc.num_div_denom`) is a constant polynomial. -/
theorem exists_algebraMap_eq_of_natDegree_eq_zero {F : Type*} [Field F] {f : RatFunc F}
    (h1 : f.num.natDegree = 0) (h2 : f.denom.natDegree = 0) :
    ∃ c : F, f = algebraMap F (RatFunc F) c := by
  -- `denom` is monic, so a denominator of degree zero is `1`.
  have hdenom : f.denom = 1 := (RatFunc.monic_denom f).natDegree_eq_zero.mp h2
  -- A numerator of degree zero is a constant polynomial.
  have hnum : f.num = Polynomial.C (f.num.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h1
  -- Write `f` in reduced form; with `denom = 1` and `num` constant it is the constant
  -- rational function whose value is the constant coefficient of `num`.
  have key : (algebraMap (Polynomial F) (RatFunc F) f.num) /
      (algebraMap (Polynomial F) (RatFunc F) f.denom)
      = algebraMap F (RatFunc F) (f.num.coeff 0) := by
    conv_lhs => rw [hnum, hdenom, map_one, div_one, RatFunc.algebraMap_C]
    rw [RatFunc.algebraMap_eq_C]
  exact ⟨f.num.coeff 0, (RatFunc.num_div_denom f).symm.trans key⟩

end Work.Genus.Main
