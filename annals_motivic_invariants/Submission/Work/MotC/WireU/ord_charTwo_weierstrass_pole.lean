import Mathlib
import Submission.Work.Genus.Defs
import Submission.Work.Genus.Order.min_ord_le_ord_add
import Submission.Work.Genus.Order.ord_add_eq_of_lt
import Submission.Work.Genus.Order.ord_pow
import Submission.Work.Genus.Order.ord_C_mul
import Submission.Work.Genus.Order.ord_aeval_of_neg
import Submission.Work.Genus.Order.ord_mul
import Submission.Work.Genus.Order.ord_sum_gt
import Submission.Work.Genus.Order.ord_aeval_nonneg
import Submission.Work.Genus.NumDenom.num_denom_eq_of_isCoprime
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pole of a Weierstrass equation in characteristic `2`

For an irreducible `π ∈ K[X]` (a finite place of `ℙ¹ = K(t)`) and a solution `(x, y)` of the
(characteristic-`2`) Weierstrass equation

`y ^ 2 + a₁ x y + a₃ y = x ^ 3 + a₂ x ^ 2 + a₄ x + a₆`

over `K(t)`, if `x` has a pole at `π` then `2 ∣ ord π x` and `2 * ord π y = 3 * ord π x`.  This is
the local Newton-polygon analysis of the Weierstrass equation: the leading terms `x ^ 3` and
`y ^ 2` must balance, forcing the order of `y` to be `3/2` of the order of `x` (with sign).

The argument is elementary and works in any characteristic; the case `CharP K 2` is the one the
`Wire123` characteristic-`2` descent needs (where the "complete the square" substitution
`w = 2y + a₁ x + a₃` degenerates).

## Route

Write `R = x ^ 3 + a₂ x ^ 2 + a₄ x + a₆` and `c = a₁ x + a₃`; the equation is `y ^ 2 + y c = R`,
i.e. `y * c = R - y ^ 2`.

* `ord π R = 3 * ord π x`: the term `x ^ 3` has order `3 μ` (`μ = ord π x < 0`) and strictly
  dominates the rest (`ord π (a₂ x² + a₄ x + a₆) > 3 μ`).
* `ord π x ≤ ord π c`: `ord π (a₁ x) ≥ μ` and `ord π a₃ ≥ 0 > μ`.
* Case `c = 0`: then `R = y ^ 2`, so `3 μ = ord π R = 2 * ord π y`.
* Case `c ≠ 0`: then `ord π (R - y ^ 2) = ord π (y * c) = ord π y + ord π c ≥ ord π y + μ`, and a
  three-way case split on `2 * ord π y` versus `3 μ` gives a contradiction unless they are equal.
-/

namespace Work.MotC.WireU

open Polynomial

/-- **Order of the negative.** `ord π (-f) = ord π f`: the reduced form of `-f` is
`(-f.num) / f.denom`, and `multiplicity π (-g) = multiplicity π g`. -/
theorem ord_neg {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π) (f : RatFunc F) :
    Work.Genus.ord π (-f) = Work.Genus.ord π f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [neg_zero]
  have hne : -f ≠ 0 := neg_ne_zero.mpr hf
  have h1 : (-f).num ≠ 0 := RatFunc.num_ne_zero hne
  have h2 : (-f).denom ≠ 0 := RatFunc.denom_ne_zero (-f)
  have h3 : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have h4 : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have key := congrArg (fun p : Polynomial F => (multiplicity π p : ℤ)) (RatFunc.num_denom_neg f)
  rw [Work.Genus.Order.multiplicity_mul_int hπ.prime h1 h3,
      Work.Genus.Order.multiplicity_mul_int hπ.prime (neg_ne_zero.mpr h4) h2,
      multiplicity_neg] at key
  simp only [Work.Genus.ord]
  linarith

/-- The order of a constant rational function is `0`. -/
theorem ord_algebraMap_const {F : Type*} [Field F] (π : Polynomial F) (a : F) :
    Work.Genus.ord π (algebraMap F (RatFunc F) a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [← mul_one (algebraMap F (RatFunc F) a), Work.Genus.Order.ord_C_mul ha (1 : RatFunc F),
      Work.Genus.Order.ord_one]

/-- **Lower bound for `a · x ^ k`.** For `ord π x ≤ 0`, the monomial `a * x ^ k` has order at least
`k * ord π x` (with equality when `a ≠ 0` and `x ≠ 0`; a vanishing term has order `0 > k μ`). -/
theorem ord_const_mul_pow_ge {F : Type*} [Field F] {π : Polynomial F} (hπ : Irreducible π)
    {x : RatFunc F} (hmu : Work.Genus.ord π x ≤ 0) (a : F) (k : ℕ) :
    (k : ℤ) * Work.Genus.ord π x ≤ Work.Genus.ord π (algebraMap F (RatFunc F) a * x ^ k) := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, zero_mul, Work.Genus.Order.ord_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg k) hmu
  · rcases eq_or_ne x 0 with rfl | hx
    · rw [Work.Genus.Order.ord_zero] at hmu
      rcases k with _ | k
      · simp only [pow_zero, mul_one, Nat.cast_zero, zero_mul]
        rw [ord_algebraMap_const]
      · rw [zero_pow (Nat.succ_ne_zero k), mul_zero, Work.Genus.Order.ord_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hmu
    · have ha' : algebraMap F (RatFunc F) a ≠ 0 := by
        rw [RatFunc.algebraMap_eq_C]
        exact fun h => ha (RatFunc.C_injective (by simpa using h))
      rw [Work.Genus.Order.ord_mul hπ ha' (pow_ne_zero k hx), Work.Genus.Order.ord_pow hπ hx k,
        ord_algebraMap_const, zero_add]

/-- **Two-term strict ultrametric bound.** If both summands have order bigger than a negative
integer `c`, so does their sum. -/
theorem ord_add_gt {F : Type*} [Field F] {π : Polynomial F} {c : ℤ} (hc : c < 0) (hπ : Irreducible π)
    {u v : RatFunc F} (hu : c < Work.Genus.ord π u) (hv : c < Work.Genus.ord π v) :
    c < Work.Genus.ord π (u + v) := by
  by_cases huv : u + v = 0
  · rw [huv, Work.Genus.Order.ord_zero]; exact hc
  · by_cases hu0 : u = 0
    · rw [hu0, zero_add]; exact hv
    · by_cases hv0 : v = 0
      · rw [hv0, add_zero]; exact hu
      · exact lt_of_lt_of_le (lt_min hu hv) (Work.Genus.Order.min_ord_le_ord_add hπ hu0 hv0 huv)

/-- **Two-term non-archimedean lower bound.** If both summands have order at least a non-positive
integer `c`, so does their sum. -/
theorem ord_add_ge_of_nonpos {F : Type*} [Field F] {π : Polynomial F} {c : ℤ} (hc : c ≤ 0)
    (hπ : Irreducible π) {u v : RatFunc F} (hu : c ≤ Work.Genus.ord π u)
    (hv : c ≤ Work.Genus.ord π v) : c ≤ Work.Genus.ord π (u + v) := by
  by_cases huv : u + v = 0
  · rw [huv, Work.Genus.Order.ord_zero]; exact hc
  · by_cases hu0 : u = 0
    · rw [hu0, zero_add]; exact hv
    · by_cases hv0 : v = 0
      · rw [hv0, add_zero]; exact hu
      · exact le_trans (le_min hu hv) (Work.Genus.Order.min_ord_le_ord_add hπ hu0 hv0 huv)

theorem ord_charTwo_weierstrass_pole {K : Type*} [Field K] [CharP K 2] (a₁ a₂ a₃ a₄ a₆ : K) {x y : RatFunc K}
    (h : y ^ 2 + algebraMap K (RatFunc K) a₁ * x * y + algebraMap K (RatFunc K) a₃ * y
      = x ^ 3 + algebraMap K (RatFunc K) a₂ * x ^ 2 + algebraMap K (RatFunc K) a₄ * x
        + algebraMap K (RatFunc K) a₆)
    {π : Polynomial K} (hπ : Irreducible π) (hx : Work.Genus.ord π x < 0) :
    (2 : ℤ) ∣ Work.Genus.ord π x ∧ 2 * Work.Genus.ord π y = 3 * Work.Genus.ord π x := by
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, Work.Genus.Order.ord_zero] at hx
    exact absurd hx (lt_irrefl 0)
  set rest : RatFunc K := algebraMap K (RatFunc K) a₂ * x ^ 2
      + algebraMap K (RatFunc K) a₄ * x + algebraMap K (RatFunc K) a₆ with hrest
  set R : RatFunc K := x ^ 3 + rest with hR
  set c : RatFunc K := algebraMap K (RatFunc K) a₁ * x + algebraMap K (RatFunc K) a₃ with hc
  -- the right-hand side of `h` is `R`
  have hRh : x ^ 3 + algebraMap K (RatFunc K) a₂ * x ^ 2 + algebraMap K (RatFunc K) a₄ * x
      + algebraMap K (RatFunc K) a₆ = R := by
    rw [hR, hrest]; ring
  -- `ord π R = 3 * ord π x`: `x ^ 3` strictly dominates the rest
  have hRord : Work.Genus.ord π R = 3 * Work.Genus.ord π x := by
    have hx3 : Work.Genus.ord π (x ^ 3) = 3 * Work.Genus.ord π x := by
      rw [Work.Genus.Order.ord_pow hπ hx0 3]; ring
    have hrest_lt : 3 * Work.Genus.ord π x < Work.Genus.ord π rest := by
      rw [hrest]
      refine ord_add_gt (c := 3 * Work.Genus.ord π x) (by linarith) hπ ?_ ?_
      · refine ord_add_gt (c := 3 * Work.Genus.ord π x) (by linarith) hπ ?_ ?_
        · have h2 : (2 : ℤ) * Work.Genus.ord π x
              ≤ Work.Genus.ord π (algebraMap K (RatFunc K) a₂ * x ^ 2) :=
            ord_const_mul_pow_ge (hπ := hπ) (x := x) (le_of_lt hx) a₂ 2
          linarith
        · have h4 : (1 : ℤ) * Work.Genus.ord π x
              ≤ Work.Genus.ord π (algebraMap K (RatFunc K) a₄ * x ^ 1) :=
            ord_const_mul_pow_ge (hπ := hπ) (x := x) (le_of_lt hx) a₄ 1
          rw [pow_one] at h4
          linarith
      · rw [ord_algebraMap_const]
        linarith
    rw [hR, Work.Genus.Order.ord_add_eq_of_lt hπ (pow_ne_zero 3 hx0)
      (by rw [hx3]; exact hrest_lt)]
    exact hx3
  -- the equation gives `y * c = R - y ^ 2`
  have hkey : y * c = R - y ^ 2 := by
    rw [hc, hR, hrest]
    linear_combination (norm := first | refl_ring1 | ring1) h
  have hy_ne : y ≠ 0 := by
    intro hy0
    have hR0 : R = 0 := by
      have hh := hkey
      rw [hy0, zero_mul, pow_two, zero_mul, sub_zero] at hh
      exact hh.symm
    rw [hR0, Work.Genus.Order.ord_zero] at hRord
    linarith
  -- `ord π x ≤ ord π c`
  have hordc : Work.Genus.ord π x ≤ Work.Genus.ord π c := by
    rw [hc]
    refine ord_add_ge_of_nonpos (c := Work.Genus.ord π x) (le_of_lt hx) hπ ?_ ?_
    · have h1 : (1 : ℤ) * Work.Genus.ord π x
          ≤ Work.Genus.ord π (algebraMap K (RatFunc K) a₁ * x ^ 1) :=
        ord_const_mul_pow_ge (hπ := hπ) (x := x) (le_of_lt hx) a₁ 1
      rw [pow_one] at h1
      linarith
    · rw [ord_algebraMap_const]; linarith
  have hmain : 2 * Work.Genus.ord π y = 3 * Work.Genus.ord π x := by
    by_cases hc0 : c = 0
    · -- `c = 0`: the equation reads `R = y ^ 2`
      have hRy : R = y ^ 2 := by
        have hh := hkey
        rw [hc0, mul_zero] at hh
        exact sub_eq_zero.mp hh.symm
      have : Work.Genus.ord π R = 2 * Work.Genus.ord π y := by
        rw [hRy, Work.Genus.Order.ord_pow hπ hy_ne 2]; ring
      rw [← this, hRord]
    · have hordkey : Work.Genus.ord π (R - y ^ 2) = Work.Genus.ord π y + Work.Genus.ord π c := by
        rw [← hkey, Work.Genus.Order.ord_mul hπ hy_ne hc0]
      have hy2ord : Work.Genus.ord π (-(y ^ 2)) = 2 * Work.Genus.ord π y := by
        rw [ord_neg hπ, Work.Genus.Order.ord_pow hπ hy_ne 2]; ring
      rcases lt_trichotomy (2 * Work.Genus.ord π y) (3 * Work.Genus.ord π x) with hlt | heq | hgt
      · -- `2 * ord π y < 3 * ord π x`: then `ord π (R - y ^ 2) = 2 * ord π y`
        have hRy2 : Work.Genus.ord π (R - y ^ 2) = 2 * Work.Genus.ord π y := by
          have h2 : Work.Genus.ord π (-(y ^ 2)) < Work.Genus.ord π R := by
            rw [hy2ord, hRord]; exact hlt
          have hh := Work.Genus.Order.ord_add_eq_of_lt hπ (neg_ne_zero.mpr (pow_ne_zero 2 hy_ne)) h2
          rwa [hy2ord, show -(y ^ 2) + R = R - y ^ 2 by ring] at hh
        linarith
      · exact heq
      · -- `2 * ord π y > 3 * ord π x`: then `ord π (R - y ^ 2) = ord π R`
        have hRy2 : Work.Genus.ord π (R - y ^ 2) = Work.Genus.ord π R := by
          have h2 : Work.Genus.ord π R < Work.Genus.ord π (-(y ^ 2)) := by
            rw [hy2ord, hRord]; exact hgt
          have hne : R ≠ 0 := by
            intro h0; rw [h0, Work.Genus.Order.ord_zero] at hRord; linarith
          have hh := Work.Genus.Order.ord_add_eq_of_lt hπ hne h2
          rwa [show R + -(y ^ 2) = R - y ^ 2 by ring] at hh
        linarith
  refine ⟨?_, hmain⟩
  have h3 : (2 : ℤ) ∣ 3 * Work.Genus.ord π x := ⟨Work.Genus.ord π y, by linarith⟩
  exact (by norm_num : IsCoprime (2:ℤ) 3).dvd_of_dvd_mul_left h3

end Work.MotC.WireU
