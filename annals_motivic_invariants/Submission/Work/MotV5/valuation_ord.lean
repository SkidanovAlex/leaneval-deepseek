import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.ord_mul
import Submission.Work.Genus.Order.min_ord_le_ord_add
import Submission.Work.Genus.Order.ord_C_mul
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The valuation of `M(t)` at the place of an irreducible polynomial

For an irreducible `π ∈ M[X]`, the order of vanishing `Work.Genus.ord π ·` at the place of `π` is a
discrete valuation of the rational function field `M(t) = RatFunc M`, with the usual convention
that the *positive* values of `ord` are the zeros of the function (rather than its poles).  This
file constructs the corresponding `ℤᵐ⁰`-valued valuation

`v x = if x = 0 then 0 else exp (-(ord π x))`

and proves that it is trivial on the constants `M` (so that it is a place of `M(t)/M`), together
with the two translation identities

* `v x ≤ 1 ↔ 0 ≤ ord π x` (regularity at the place),
* `1 < v x ↔ ord π x < 0` (a pole at the place),

which are the form in which the "valuation attached to an irreducible polynomial" is consumed by
the rest of the development (route V, `theorem_1_2_2` / `theorem_1_2_3`).

The mathematical content is entirely in the three order lemmas imported above: additivity of `ord`
on products (`ord_mul`), the non-archimedean inequality (`min_ord_le_ord_add`), and the fact that a
non-zero constant has order `0` (`ord_C_mul`).  The two cases `x = 0` are handled by the `if`, and
all comparisons take place in the ordered group with zero `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`,
where `WithZero.exp` is an order embedding of `ℤ` onto the non-zero elements.
-/

open scoped WithZero

namespace Work.MotV5

open Classical

variable {M : Type*} [Field M]

/-! ## Orders of the elementary elements -/

/-- The constant rational function `1` has order of vanishing `0` at any place. -/
lemma ord_one (π : Polynomial M) : Work.Genus.ord π (1 : RatFunc M) = 0 := by
  simp [Work.Genus.ord, RatFunc.num_one, RatFunc.denom_one]

/-- The zero rational function has order of vanishing `0` (the convention of
`Polynomial.multiplicity`; `ord π ·` is *not* a valuation without this normalization). -/
lemma ord_zero (π : Polynomial M) : Work.Genus.ord π (0 : RatFunc M) = 0 := by
  simp [Work.Genus.ord, RatFunc.num_zero, RatFunc.denom_zero]

/-- A non-zero constant of `M` has order of vanishing `0` at the place of any `π`: it is a unit at
every place.  This is the content of `ord_C_mul` together with `ord_one`. -/
lemma ord_algebraMap (π : Polynomial M) {c : M} (hc : c ≠ 0) :
    Work.Genus.ord π (algebraMap M (RatFunc M) c) = 0 := by
  have h := Work.Genus.Order.ord_C_mul (π := π) hc (1 : RatFunc M)
  rw [ord_one, mul_one] at h
  exact h

/-- `WithZero.exp` is an order isomorphism onto the non-zero elements of `ℤᵐ⁰`, hence it preserves
binary maxima. -/
lemma exp_max (a b : ℤ) :
    WithZero.exp (max a b) = max (WithZero.exp a) (WithZero.exp b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (WithZero.exp_le_exp.mpr h)]
  · rw [max_eq_left h, max_eq_left (WithZero.exp_le_exp.mpr h)]

/-! ## The valuation function -/

/-- The valuation of `M(t)` at the place of `π`, as a `ℤᵐ⁰`-valued function: `0` is sent to the
zero of `ℤᵐ⁰` (the "infinite" value) and every other element `x` to `exp (-(ord π x))`, so that
positive order (a zero of `x`) corresponds to a value `< 1` and a pole to a value `> 1`. -/
noncomputable def valDef (π : Polynomial M) (x : RatFunc M) : WithZero (Multiplicative ℤ) :=
  if x = 0 then 0 else WithZero.exp (-(Work.Genus.ord π x))

lemma valDef_zero (π : Polynomial M) : valDef π (0 : RatFunc M) = 0 := by
  rw [valDef]; simp

lemma valDef_of_ne {π : Polynomial M} {x : RatFunc M} (hx : x ≠ 0) :
    valDef π x = WithZero.exp (-(Work.Genus.ord π x)) := by
  rw [valDef]; simp [hx]

/-- Multiplicativity: this is the additivity of `ord` on products, transported through the order
isomorphism `WithZero.exp`. -/
lemma valDef_mul (π : Polynomial M) (hπ : Irreducible π) (x y : RatFunc M) :
    valDef π (x * y) = valDef π x * valDef π y := by
  by_cases hx : x = 0
  · subst hx; simp [valDef]
  · by_cases hy : y = 0
    · subst hy; simp [valDef]
    · have hxy : x * y ≠ 0 := mul_ne_zero hx hy
      rw [valDef_of_ne hxy, valDef_of_ne hx, valDef_of_ne hy, ← WithZero.exp_add,
        Work.Genus.Order.ord_mul hπ hx hy]
      congr 1
      first | refl_ring1 | ring

/-- The non-archimedean inequality: this is `min_ord_le_ord_add`, transported through the order
isomorphism `WithZero.exp`. -/
lemma valDef_add_le (π : Polynomial M) (hπ : Irreducible π) (x y : RatFunc M) :
    valDef π (x + y) ≤ max (valDef π x) (valDef π y) := by
  by_cases hxy : x + y = 0
  · rw [hxy, valDef_zero]
    exact zero_le
  · by_cases hx : x = 0
    · subst hx
      rw [zero_add, valDef_zero]
      exact le_max_right _ _
    · by_cases hy : y = 0
      · subst hy
        rw [add_zero, valDef_zero]
        exact le_max_left _ _
      · rw [valDef_of_ne hxy, valDef_of_ne hx, valDef_of_ne hy,
          ← exp_max (-(Work.Genus.ord π x)) (-(Work.Genus.ord π y))]
        exact WithZero.exp_le_exp.mpr (by
          have h := Work.Genus.Order.min_ord_le_ord_add hπ hx hy hxy
          omega)

/-- **The valuation of `M(t)` at the place of an irreducible `π`.** -/
noncomputable def placeValuationRatFunc (π : Polynomial M) (hπ : Irreducible π) :
    Valuation (RatFunc M) (WithZero (Multiplicative ℤ)) where
  toFun := valDef π
  map_zero' := valDef_zero π
  map_one' := by
    rw [valDef_of_ne (x := (1 : RatFunc M)) one_ne_zero, ord_one, neg_zero,
      WithZero.exp_zero]
  map_mul' := valDef_mul π hπ
  map_add_le_max' := valDef_add_le π hπ

theorem valuation_ord {M : Type*} [Field M] (π : Polynomial M) (hπ : Irreducible π) :
    ∃ v : Valuation (RatFunc M) (WithZero (Multiplicative ℤ)),
      Work.MotV.TrivOn M v ∧
      (∀ x : RatFunc M, v x ≤ 1 ↔ 0 ≤ Work.Genus.ord π x) ∧
      (∀ x : RatFunc M, 1 < v x ↔ Work.Genus.ord π x < 0) := by
  classical
  refine ⟨placeValuationRatFunc π hπ, ?_, ?_, ?_⟩
  · -- trivial on the constants: a non-zero constant has order `0`, so value `exp 0 = 1`
    intro c hc
    show valDef π (algebraMap M (RatFunc M) c) = 1
    rw [valDef_of_ne (by simpa using (algebraMap M (RatFunc M)).injective.ne hc),
      ord_algebraMap π hc, neg_zero, WithZero.exp_zero]
  · intro x
    show valDef π x ≤ 1 ↔ 0 ≤ Work.Genus.ord π x
    by_cases hx : x = 0
    · subst hx; rw [valDef_zero, ord_zero]; simp
    · rw [valDef_of_ne hx, WithZero.exp_le_one_iff]; omega
  · intro x
    show 1 < valDef π x ↔ Work.Genus.ord π x < 0
    by_cases hx : x = 0
    · subst hx; rw [valDef_zero, ord_zero]; simp
    · rw [valDef_of_ne hx, WithZero.one_lt_exp_iff]; omega

end Work.MotV5
