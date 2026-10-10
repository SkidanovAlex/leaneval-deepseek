import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.NumDenom

/-- **Reduced-form uniqueness for `RatFunc`.**  If `q ≠ 0` is monic and coprime to `p`, then the
fraction `p / q` is already the canonical reduced form of `x`: its `RatFunc.num` is `p` and its
`RatFunc.denom` is `q`.  (`RatFunc.denom` is normalized to be monic, so the monicity hypothesis is
what pins the unit down; the coprimality is what makes `p / q` reduced.) -/
theorem num_denom_eq_of_isCoprime {F : Type*} [Field F] {x : RatFunc F}
    {p q : Polynomial F}
    (hq : q ≠ 0) (hcop : IsCoprime p q) (hmon : q.Monic)
    (hx : algebraMap (Polynomial F) (RatFunc F) p / algebraMap (Polynomial F) (RatFunc F) q = x) :
    x.num = p ∧ x.denom = q := by
  -- Cross-multiplication: `num x * q = p * denom x`.
  have hcross : x.num * q = p * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr hx.symm
  -- `denom x` divides `q`, say `q = denom x * a`.
  obtain ⟨a, ha⟩ : ∃ a, q = x.denom * a := (RatFunc.denom_dvd hq).mpr ⟨p, hx.symm⟩
  -- From the cross-multiplication, `num x * a = p`.
  have hnum : x.num * a = p := by
    have h1 : x.num * (x.denom * a) = p * x.denom := by rw [← ha]; exact hcross
    have h2 : (x.num * a) * x.denom = p * x.denom := by rw [← h1]; ring
    exact mul_right_cancel₀ (RatFunc.denom_ne_zero x) h2
  -- Rewriting `p = num x * a` and `q = denom x * a` into the coprimality hypothesis.
  have hcop' : IsCoprime (x.num * a) (x.denom * a) := by
    rw [hnum, ← ha]; exact hcop
  -- ... shows that the common factor `a` is a unit.
  have hunit : IsUnit a := hcop'.isUnit_of_dvd' (dvd_mul_left a x.num) (dvd_mul_left a x.denom)
  -- ... and monicity of `q = denom x * a` forces `a` to be monic as well, so `a = 1`.
  have hamon : a.Monic := (RatFunc.monic_denom x).of_mul_monic_left (by rw [← ha]; exact hmon)
  have ha1 : a = 1 := hamon.eq_one_of_isUnit hunit
  rw [ha1, mul_one] at hnum
  exact ⟨hnum, by rw [ha, ha1, mul_one]⟩

end Work.Genus.NumDenom
