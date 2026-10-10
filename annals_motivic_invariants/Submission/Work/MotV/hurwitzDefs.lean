import Mathlib
import ChallengeDeps
import Submission.Work.MotV.Defs
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_mul
import Submission.Work.Genus.Order.ord_pow

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Shared vocabulary of the Hurwitz-lite node `Work.MotV.hurwitz_five_ratFunc`

This file holds the definitions and the easy lemmas that the proof of
`Work.MotV.hurwitz_five_ratFunc` and its helper lemmas share.

* `ordc c f` — the order of vanishing of `f : M(y)` at the point `c` of the affine line, i.e. the
  multiplicity of `X - C c` in the numerator minus its multiplicity in the denominator of `f`
  (the place `X - C c` of the rational function field).
* `FifthHyp f` — the pointwise form of the hypothesis of `hurwitz_five_ratFunc`: at every point
  `c` of the affine line, both `ordc c f` and `ordc c (f - 1)` are divisible by `5`.
* `placeSet f` — the (finite) set of points of the affine line containing all the zeros and poles
  relevant to the counting argument for the derivative of `f`.
* `sum_rootMultiplicity_eq_natDegree` — the elementary `ℙ¹` fact that for `M` algebraically closed
  the multiplicities of the roots of a non-zero polynomial add up to its degree.
-/

open Polynomial
open scoped WithZero

namespace Work.MotV
noncomputable section

/-! ## §1 The order of vanishing at a finite place -/

/-- **The order of vanishing at the finite place `c`.**  For `f : M(y)` with numerator `f.num` and
denominator `f.denom` (the reduced form of Mathlib's `RatFunc`), `ordc c f` is the multiplicity of
`X - C c` in `f.num` minus its multiplicity in `f.denom`: positive means a zero, negative a pole.
By the convention on `Polynomial.rootMultiplicity` the value at `f = 0` is `0`. -/
def ordc {M : Type*} [Field M] (c : M) (f : RatFunc M) : ℤ :=
  (f.num.rootMultiplicity c : ℤ) - (f.denom.rootMultiplicity c : ℤ)

/-- `ordc c` agrees with the order of vanishing at the place of the irreducible `X - C c` as
defined in the genus chapter (`Work.Genus.ord`). -/
theorem ordc_eq_ord {M : Type*} [Field M] [DecidableEq M] {c : M} {f : RatFunc M} (hf : f ≠ 0) :
    ordc c f = Work.Genus.ord (X - C c) f := by
  rw [ordc, Work.Genus.ord, rootMultiplicity_eq_multiplicity f.num c,
    rootMultiplicity_eq_multiplicity f.denom c, ite_eq_right (RatFunc.num_ne_zero hf),
    ite_eq_right (RatFunc.denom_ne_zero f)]

/-- Additivity of the order of vanishing at a finite place on products. -/
theorem ordc_mul {M : Type*} [Field M] [DecidableEq M] {c : M} {f g : RatFunc M} (hf : f ≠ 0)
    (hg : g ≠ 0) : ordc c (f * g) = ordc c f + ordc c g := by
  rw [ordc_eq_ord (mul_ne_zero hf hg), ordc_eq_ord hf, ordc_eq_ord hg,
    Work.Genus.Order.ord_mul (irreducible_X_sub_C c) hf hg]

/-- The order of vanishing at a finite place of a power. -/
theorem ordc_pow {M : Type*} [Field M] [DecidableEq M] {c : M} {f : RatFunc M} (hf : f ≠ 0)
    (n : ℕ) : ordc c (f ^ n) = n * ordc c f := by
  rw [ordc_eq_ord (pow_ne_zero n hf), ordc_eq_ord hf,
    Work.Genus.Order.ord_pow (irreducible_X_sub_C c) hf n]

/-- The order of vanishing at a finite place of a constant. -/
theorem ordc_algebraMap {M : Type*} [Field M] {c : M} (k : M) :
    ordc c (algebraMap M (RatFunc M) k) = 0 := by
  have hnum : (algebraMap M (RatFunc M) k).num = C k := by
    rw [RatFunc.algebraMap_eq_C, RatFunc.num_C]
  have hden : (algebraMap M (RatFunc M) k).denom = 1 := by
    rw [RatFunc.algebraMap_eq_C, RatFunc.denom_C]
  rw [ordc, hnum, hden]
  simp [Polynomial.rootMultiplicity_C]

/-! ## §2 The pointwise hypothesis and the finite set of places -/

/-- **The pointwise hypothesis of the Hurwitz-lite node.**  At every point `c` of the affine line
both the order of vanishing of `f` and that of `f - 1` are divisible by `5`. -/
def FifthHyp {M : Type*} [Field M] (f : RatFunc M) : Prop :=
  ∀ c : M, (5 : ℤ) ∣ ordc c f ∧ (5 : ℤ) ∣ ordc c (f - 1)

/-- The finite set of points of the affine line that carries all the information needed by the
counting argument for `deriv f`: the roots of the numerator, of the denominator, of their
difference, and of the numerator `f' g - f g'` of the derivative. -/
def placeSet {M : Type*} [Field M] [DecidableEq M] (f : RatFunc M) : Finset M :=
  (f.num.roots + f.denom.roots + (f.num - f.denom).roots
    + (f.num.derivative * f.denom - f.num * f.denom.derivative).roots).toFinset

/-! ## §3 The multiplicities of the roots of a polynomial add up to its degree -/

/-- **The multiplicities of the roots of a non-zero polynomial over an algebraically closed field
add up to its degree.**  Route: `IsAlgClosed.splits` gives `f.natDegree = f.roots.card`, and the
cardinality of the multiset of roots is the sum over the distinct roots of their multiplicities
(`Multiset.toFinset_sum_count_eq` and `Polynomial.count_roots`). -/
theorem sum_rootMultiplicity_eq_natDegree {M : Type*} [Field M] [IsAlgClosed M] [DecidableEq M]
    (P : Polynomial M) (_hP : P ≠ 0) :
    ∑ c ∈ P.roots.toFinset, (P.rootMultiplicity c : ℤ) = (P.natDegree : ℤ) := by
  have hcard : P.roots.card = P.natDegree := (IsAlgClosed.splits P).natDegree_eq_card_roots.symm
  have hnat : ∑ c ∈ P.roots.toFinset, P.rootMultiplicity c = P.natDegree := by
    rw [← hcard, ← Multiset.toFinset_sum_count_eq P.roots]
    exact Finset.sum_congr rfl fun c _ => by rw [Polynomial.count_roots]
  rw [← hnat]
  push_cast
  rfl

end
end Work.MotV
