import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Multiplication by a non-zero constant does not change the order of vanishing

`Work.Genus.ord π f` is defined as `multiplicity π f.num - multiplicity π f.denom`, where
`f.num`, `f.denom` are Mathlib's reduced numerator/denominator of the rational function `f`
(`f.denom` is monic and coprime to `f.num`).  Multiplying `f` by a non-zero constant `c` — i.e. by
the polynomial `C c`, a *unit* of `F[X]` — leaves the reduced form unchanged up to that unit:
indeed, if `f = p/q` with `q` monic and `IsCoprime p q`, then `u * f = (u*p)/q` and `(u*p, q)` is
again such a pair, so by uniqueness of the reduced form `(num, denom)` of a rational function
(`num_denom_eq_of_isCoprime`) one gets `(u * f).num = u * f.num` and `(u * f).denom = f.denom`.
Finally `multiplicity π` is insensitive to a unit factor on the left
(`multiplicity_mul_unit_left`), which concludes.

The lemmas are stated for an arbitrary unit `u : F[X]`, the case at hand being `u = C c`.
-/

namespace Work.Genus.Order

open Polynomial

/-- The multiplicity of `π` in a product is unchanged by a unit factor: for a unit `u` of the
coefficient ring (`u = C a`, `a ≠ 0`, when that ring is a field) one has `u ^ n ∣ u * b ↔ u ^ n ∣ b`
for every `n`, and hence the same `emultiplicity`, hence the same `multiplicity`. -/
lemma multiplicity_mul_unit_left {F : Type*} [Field F] {π u b : Polynomial F} (hu : IsUnit u) :
    multiplicity π (u * b) = multiplicity π b := by
  have h : emultiplicity π (u * b) = emultiplicity π b :=
    emultiplicity_eq_emultiplicity_iff.mpr (fun n => IsUnit.dvd_mul_left hu)
  simpa [multiplicity] using congrArg ENat.toNat h

/-- **Uniqueness of the reduced form.**  If `x = p/q` in `F(t)` with `q ≠ 0` monic and
`IsCoprime p q`, then `p` and `q` are exactly Mathlib's normalized numerator and denominator of
`x`.  Route: `RatFunc.num_mul_eq_mul_denom_iff` turns `x = p/q` into
`x.num * q = p * x.denom`, and coprimality converts the two factorizations into the mutual
divisibility `q ∣ x.denom` and `x.denom ∣ q`; both are monic, so they are equal
(`eq_of_monic_of_associated`), and cancelling `x.denom` gives `p = x.num`. -/
lemma num_denom_eq_of_isCoprime {F : Type*} [Field F] {x : RatFunc F} {p q : Polynomial F}
    (hq : q ≠ 0) (hqm : q.Monic) (hcop : IsCoprime p q)
    (hx : x = algebraMap (Polynomial F) (RatFunc F) p / algebraMap (Polynomial F) (RatFunc F) q) :
    p = x.num ∧ q = x.denom := by
  have key : x.num * q = p * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr hx
  have hq_dvd : q ∣ x.denom :=
    hcop.symm.dvd_of_dvd_mul_left (by rw [← key]; exact dvd_mul_left q x.num)
  have hd_dvd : x.denom ∣ q :=
    (RatFunc.isCoprime_num_denom x).symm.dvd_of_dvd_mul_left
      (by rw [key]; exact dvd_mul_left x.denom p)
  have hqeq : q = x.denom :=
    eq_of_monic_of_associated hqm (RatFunc.monic_denom x) (associated_of_dvd_dvd hq_dvd hd_dvd)
  have hpeq : p = x.num := by
    rw [hqeq] at key
    exact mul_right_cancel₀ (RatFunc.denom_ne_zero x) key.symm
  exact ⟨hpeq, hqeq⟩

/-- Multiplying a rational function by a unit `u` of `F[X]` multiplies its numerator by `u` and
leaves its denominator unchanged: `(u f).num = u f.num`, `(u f).denom = f.denom`.  This is the
normalization statement behind `ord π (u f) = ord π f`. -/
lemma num_denom_mul_unit {F : Type*} [Field F] {u : Polynomial F} (hu : IsUnit u)
    (f : RatFunc F) :
    (algebraMap (Polynomial F) (RatFunc F) u * f).num = u * f.num ∧
      (algebraMap (Polynomial F) (RatFunc F) u * f).denom = f.denom := by
  have hcop : IsCoprime (u * f.num) (f.denom) :=
    (isCoprime_mul_unit_left_left hu f.num f.denom).mpr (RatFunc.isCoprime_num_denom f)
  have hx : algebraMap (Polynomial F) (RatFunc F) u * f
      = algebraMap (Polynomial F) (RatFunc F) (u * f.num)
        / algebraMap (Polynomial F) (RatFunc F) (f.denom) := by
    conv_lhs => rw [← RatFunc.num_div_denom f]
    rw [map_mul, mul_div_assoc]
  obtain ⟨h1, h2⟩ : u * f.num = (algebraMap (Polynomial F) (RatFunc F) u * f).num ∧
      f.denom = (algebraMap (Polynomial F) (RatFunc F) u * f).denom :=
    num_denom_eq_of_isCoprime (RatFunc.denom_ne_zero f) (RatFunc.monic_denom f) hcop hx
  exact ⟨h1.symm, h2.symm⟩

/-- Multiplication by a non-zero constant does not change the order of vanishing at a place. -/
theorem ord_C_mul {F : Type*} [Field F] {π : Polynomial F} {c : F} (hc : c ≠ 0) (f : RatFunc F) :
    Work.Genus.ord π (algebraMap F (RatFunc F) c * f) = Work.Genus.ord π f := by
  have hu : IsUnit (Polynomial.C c : Polynomial F) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hmap : algebraMap F (RatFunc F) c = algebraMap (Polynomial F) (RatFunc F) (Polynomial.C c) := by
    rw [RatFunc.algebraMap_eq_C]; rfl
  obtain ⟨hnum, hden⟩ := num_denom_mul_unit hu f
  rw [hmap, Work.Genus.ord, Work.Genus.ord, hnum, hden, multiplicity_mul_unit_left hu]

end Work.Genus.Order
