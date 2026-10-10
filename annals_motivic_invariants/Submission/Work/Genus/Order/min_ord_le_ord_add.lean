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

open Polynomial

/-- **The polynomial-level non-archimedean inequality for `Polynomial.multiplicity`** (with values in
`ℕ`): for an irreducible `π` and polynomials `a`, `b` with `a + b ≠ 0`, the smaller of the
multiplicities of `π` in `a` and in `b` is at most its multiplicity in `a + b`.

Both `π ^ m ∣ a` and `π ^ m ∣ b` for `m = min (multiplicity π a) (multiplicity π b)`
(`pow_dvd_of_le_multiplicity` and `min_le_left`/`min_le_right`), hence `π ^ m ∣ a + b`; since
`a + b ≠ 0` the multiplicity of `π` in `a + b` is finite (`FiniteMultiplicity.of_not_isUnit`), and
the claim follows from `FiniteMultiplicity.le_multiplicity_of_pow_dvd`. -/
theorem min_multiplicity_le_multiplicity_add {F : Type*} [Field F] {π a b : Polynomial F}
    (hπ : Irreducible π) (hab : a + b ≠ 0) :
    min (multiplicity π a) (multiplicity π b) ≤ multiplicity π (a + b) := by
  have hfin : FiniteMultiplicity π (a + b) :=
    FiniteMultiplicity.of_not_isUnit hπ.not_isUnit hab
  exact hfin.le_multiplicity_of_pow_dvd (by
    apply dvd_add
    · exact pow_dvd_of_le_multiplicity (min_le_left _ _)
    · exact pow_dvd_of_le_multiplicity (min_le_right _ _))

/-- The `ℤ`-valued form of `min_multiplicity_le_multiplicity_add`, obtained by pushing the
(monotone) coercion `ℕ → ℤ` through `min` (`Nat.cast_min`). -/
theorem min_multiplicity_le_multiplicity_add_int {F : Type*} [Field F] {π a b : Polynomial F}
    (hπ : Irreducible π) (hab : a + b ≠ 0) :
    min (multiplicity π a : ℤ) (multiplicity π b : ℤ) ≤ (multiplicity π (a + b) : ℤ) := by
  rw [← Nat.cast_min]
  exact_mod_cast min_multiplicity_le_multiplicity_add hπ hab

/-- The elementary arithmetic rearrangement underlying the non-archimedean inequality: translating
both arguments of a `min` by the same constant, and distributing the subtraction.  Concretely,
`min (A + D) (B + C) ≤ E` implies `min (A - B) (C - D) ≤ E - B - D`; both sides are the same
disjunction of linear inequalities (`min_le_iff`). -/
theorem min_sub_le {A B C D E : ℤ} (h : min (A + D) (B + C) ≤ E) :
    min (A - B) (C - D) ≤ E - B - D := by
  rw [min_le_iff] at h ⊢
  rcases h with h | h
  · left; linarith
  · right; linarith

/-- The non-archimedean inequality for the order of vanishing at the place of an irreducible `π`
of `F(t)`. -/
theorem min_ord_le_ord_add {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π)
    {f g : RatFunc F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (Work.Genus.ord π f) (Work.Genus.ord π g) ≤ Work.Genus.ord π (f + g) := by
  have hnum_f : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden_f : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hnum_g : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hden_g : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hq : f.denom * g.denom ≠ 0 := mul_ne_zero hden_f hden_g
  have hp : f.num * g.denom + f.denom * g.num ≠ 0 :=
    RatFunc.num_mul_denom_add_denom_mul_num_ne_zero hfg
  -- The non-archimedean inequality seen through the `π`-multiplicities of the numerators and
  -- denominators of `f` and `g`.  Applying it to `f.num * g.denom` and `f.denom * g.num` and
  -- rewriting the multiplicities of the products (`multiplicity_mul_int`) gives
  -- `min (A + D) (B + C) ≤ multiplicity π (f.num * g.denom + f.denom * g.num)`.
  have hmin : min ((multiplicity π f.num : ℤ) + (multiplicity π g.denom : ℤ))
      ((multiplicity π f.denom : ℤ) + (multiplicity π g.num : ℤ))
      ≤ (multiplicity π (f.num * g.denom + f.denom * g.num) : ℤ) := by
    have h := min_multiplicity_le_multiplicity_add_int (π := π) hπ hp
    rwa [multiplicity_mul_int hπ.prime hnum_f hden_g,
         multiplicity_mul_int hπ.prime hden_f hnum_g] at h
  -- `f + g` written as the explicit fraction `p / q`.
  have hfrac : f + g =
      algebraMap (Polynomial F) (RatFunc F) (f.num * g.denom + f.denom * g.num)
        / algebraMap (Polynomial F) (RatFunc F) (f.denom * g.denom) :=
    (RatFunc.num_mul_eq_mul_denom_iff hq).mp (RatFunc.num_denom_add f g)
  -- Consequently `ord π (f + g) = multiplicity π p - multiplicity π f.denom - multiplicity π g.denom`.
  have hord : Work.Genus.ord π (f + g)
      = (multiplicity π (f.num * g.denom + f.denom * g.num) : ℤ)
        - (multiplicity π f.denom : ℤ) - (multiplicity π g.denom : ℤ) := by
    rw [hfrac, ord_div hπ hp hq, multiplicity_mul_int hπ.prime hden_f hden_g]
    first | refl_ring1 | ring
  rw [hord]
  simp only [Work.Genus.ord]
  exact min_sub_le hmin

end Work.Genus.Order
