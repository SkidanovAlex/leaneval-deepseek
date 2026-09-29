import Mathlib
import Submission.Commons.Algebra.Polynomial.rootMultiplicity_add_eq_of_lt

/-!
# The order of vanishing of a rational function at a point

For a rational function `x ∈ K(X)` and a point `α ∈ K` we define
`ordAt α x : ℤ` — the order of vanishing of `x` at `α`, negative at a pole —
and develop its basic calculus: additive, inversion-negating, equal to the
root multiplicity on polynomials, and `min`-subadditive for sums.

This is the "valuation at a finite place" calculus needed by the
Frobenius/indicial (pole-order) analysis of a rational solution of a linear
differential equation.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K]

/-- **Order of vanishing at `α`** of a rational function: the multiplicity of
`α` as a root of the numerator minus its multiplicity in the denominator.
Negative values encode poles (`-ord` is the pole order). -/
def ordAt (α : K) (x : RatFunc K) : ℤ :=
  (Polynomial.rootMultiplicity α x.num : ℤ) - (Polynomial.rootMultiplicity α x.denom : ℤ)

@[simp] lemma ordAt_zero (α : K) : ordAt α (0 : RatFunc K) = 0 := by
  simp [ordAt]

lemma rootMultiplicity_C_ne_zero {c : K} (_hc : c ≠ 0) (α : K) :
    Polynomial.rootMultiplicity α (Polynomial.C c) = 0 := by
  rw [Polynomial.rootMultiplicity_eq_zero_iff]
  intro h
  exact Polynomial.C_eq_zero.mpr (by rwa [Polynomial.IsRoot.def, Polynomial.eval_C] at h)

/-- `rootMultiplicity` is invariant under association. -/
lemma rootMultiplicity_eq_of_associated {p q : Polynomial K} (h : Associated p q) (α : K) :
    Polynomial.rootMultiplicity α p = Polynomial.rootMultiplicity α q := by
  obtain ⟨u, hu⟩ := h.symm
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hc0 : c ≠ 0 := fun h0 => by rw [h0] at hc; exact not_isUnit_zero hc
  rw [← hu, ← hcu]
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hq (Polynomial.C_ne_zero.mpr hc0)),
      rootMultiplicity_C_ne_zero hc0, add_zero]

/-- On polynomials, `ordAt` is the root multiplicity. -/
@[simp] lemma ordAt_algebraMap (α : K) (p : Polynomial K) :
    ordAt α (algebraMap (Polynomial K) (RatFunc K) p) = (Polynomial.rootMultiplicity α p : ℤ) := by
  rw [ordAt, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

lemma ordAt_one (α : K) : ordAt α (1 : RatFunc K) = 0 := by
  rw [show (1 : RatFunc K) = algebraMap (Polynomial K) (RatFunc K) (1 : Polynomial K) from
      (map_one _).symm, ordAt_algebraMap,
    show (1 : Polynomial K) = Polynomial.C (1 : K) from (map_one Polynomial.C).symm,
    rootMultiplicity_C_ne_zero one_ne_zero]
  simp

/-- `ordAt` is additive. -/
lemma ordAt_mul (α : K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAt α (x * y) = ordAt α x + ordAt α y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hn1 : x.num ≠ 0 := RatFunc.num_ne_zero hx
  have hn2 : y.num ≠ 0 := RatFunc.num_ne_zero hy
  have hn3 : (x * y).num ≠ 0 := RatFunc.num_ne_zero hxy
  have hd1 : x.denom ≠ 0 := RatFunc.denom_ne_zero x
  have hd2 : y.denom ≠ 0 := RatFunc.denom_ne_zero y
  have hd3 : (x * y).denom ≠ 0 := RatFunc.denom_ne_zero (x * y)
  have h1 : Polynomial.rootMultiplicity α ((x * y).num)
      + Polynomial.rootMultiplicity α (x.denom * y.denom)
      = Polynomial.rootMultiplicity α (x.num * y.num)
      + Polynomial.rootMultiplicity α ((x * y).denom) := by
    have h := congrArg (Polynomial.rootMultiplicity α) (RatFunc.num_denom_mul x y)
    rwa [Polynomial.rootMultiplicity_mul (mul_ne_zero hn3 (mul_ne_zero hd1 hd2)),
      Polynomial.rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hn1 hn2) hd3)] at h
  have h2 : Polynomial.rootMultiplicity α (x.denom * y.denom)
      = Polynomial.rootMultiplicity α x.denom + Polynomial.rootMultiplicity α y.denom :=
    Polynomial.rootMultiplicity_mul (mul_ne_zero hd1 hd2)
  have h3 : Polynomial.rootMultiplicity α (x.num * y.num)
      = Polynomial.rootMultiplicity α x.num + Polynomial.rootMultiplicity α y.num :=
    Polynomial.rootMultiplicity_mul (mul_ne_zero hn1 hn2)
  simp only [ordAt]
  linarith

/-- `ordAt` negates under inversion. -/
lemma ordAt_inv (α : K) {x : RatFunc K} (hx : x ≠ 0) :
    ordAt α x⁻¹ = -ordAt α x := by
  rw [ordAt, ordAt,
    rootMultiplicity_eq_of_associated (RatFunc.associated_num_inv hx) α,
    rootMultiplicity_eq_of_associated (RatFunc.associated_denom_inv hx) α]
  ring

/-- `ordAt` of a division. -/
lemma ordAt_div (α : K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAt α (x / y) = ordAt α x - ordAt α y := by
  rw [div_eq_mul_inv, ordAt_mul α hx (inv_ne_zero hy), ordAt_inv α hy]
  ring

lemma ordAt_neg (α : K) (x : RatFunc K) : ordAt α (-x) = ordAt α x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h : (-1 : RatFunc K) * x = -x := by ring
    rw [← h, ordAt_mul α (neg_ne_zero.mpr one_ne_zero) hx]
    have hone : ordAt α (-1 : RatFunc K) = 0 := by
      rw [show (-1 : RatFunc K) = algebraMap (Polynomial K) (RatFunc K)
          (Polynomial.C (-1 : K)) from by rw [map_neg, map_one]; norm_num,
        ordAt_algebraMap]
      exact_mod_cast rootMultiplicity_C_ne_zero (by norm_num : (-1 : K) ≠ 0) α
    rw [hone, zero_add]

lemma ordAt_pow (α : K) (x : RatFunc K) (n : ℕ) :
    ordAt α (x ^ n) = n * ordAt α x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero, ordAt_one]; simp
    · rw [zero_pow (by omega)]
      simp
  · induction n with
    | zero => rw [pow_zero, ordAt_one]; simp
    | succ n ih => rw [pow_succ, ordAt_mul α (pow_ne_zero n hx) hx, ih]; push_cast; ring

/-- The `min` lower bound for the order of vanishing of a sum. -/
lemma min_ordAt_le_ordAt_add (α : K) {x y : RatFunc K} (hxy : x + y ≠ 0) :
    min (ordAt α x) (ordAt α y) ≤ ordAt α (x + y) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [zero_add, ordAt_zero]; exact min_le_right _ _
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [add_zero]; exact min_le_left _ _
  have hnumx : x.num ≠ 0 := RatFunc.num_ne_zero hx0
  have hnumy : y.num ≠ 0 := RatFunc.num_ne_zero hy0
  have hdx : x.denom ≠ 0 := RatFunc.denom_ne_zero x
  have hdy : y.denom ≠ 0 := RatFunc.denom_ne_zero y
  have hdax : (algebraMap (Polynomial K) (RatFunc K) x.denom) ≠ 0 := by
    simpa using hdx
  have hday : (algebraMap (Polynomial K) (RatFunc K) y.denom) ≠ 0 := by
    simpa using hdy
  have hx : x = algebraMap _ _ x.num / algebraMap _ _ x.denom := (RatFunc.num_div_denom x).symm
  have hy : y = algebraMap _ _ y.num / algebraMap _ _ y.denom := (RatFunc.num_div_denom y).symm
  have hkey : x + y = algebraMap _ _ (x.num * y.denom + y.num * x.denom)
      / algebraMap _ _ (x.denom * y.denom) := by
    conv_lhs => rw [hx, hy]
    rw [div_add_div _ _ hdax hday, map_add, map_mul, map_mul, map_mul]
    ring
  have hA0 : x.num * y.denom + y.num * x.denom ≠ 0 := by
    intro h0
    exact hxy (by rw [hkey, h0, map_zero, zero_div])
  have hAmap : (algebraMap (Polynomial K) (RatFunc K)
      (x.num * y.denom + y.num * x.denom)) ≠ 0 :=
    fun h => hA0 ((RatFunc.algebraMap_injective K) (by rw [h, map_zero]))
  have hBmap : (algebraMap (Polynomial K) (RatFunc K) (x.denom * y.denom)) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hdax hday
  have hmin := Polynomial.rootMultiplicity_add (p := x.num * y.denom)
    (q := y.num * x.denom) α hA0
  have e1 : Polynomial.rootMultiplicity α (x.num * y.denom)
      = Polynomial.rootMultiplicity α x.num + Polynomial.rootMultiplicity α y.denom :=
    Polynomial.rootMultiplicity_mul (mul_ne_zero hnumx hdy)
  have e2 : Polynomial.rootMultiplicity α (y.num * x.denom)
      = Polynomial.rootMultiplicity α y.num + Polynomial.rootMultiplicity α x.denom :=
    Polynomial.rootMultiplicity_mul (mul_ne_zero hnumy hdx)
  have e3 : Polynomial.rootMultiplicity α (x.denom * y.denom)
      = Polynomial.rootMultiplicity α x.denom + Polynomial.rootMultiplicity α y.denom :=
    Polynomial.rootMultiplicity_mul (mul_ne_zero hdx hdy)
  rw [hkey, ordAt_div α hAmap hBmap, ordAt_algebraMap, ordAt_algebraMap, e3]
  simp only [ordAt]
  push_cast
  rw [e1, e2] at hmin
  have hminZ : min (((Polynomial.rootMultiplicity α x.num : ℕ) : ℤ)
        + ((Polynomial.rootMultiplicity α y.denom : ℕ) : ℤ))
      (((Polynomial.rootMultiplicity α y.num : ℕ) : ℤ)
        + ((Polynomial.rootMultiplicity α x.denom : ℕ) : ℤ))
      ≤ ((Polynomial.rootMultiplicity α (x.num * y.denom + y.num * x.denom) : ℕ) : ℤ) := by
    exact_mod_cast hmin
  omega

/-- **Strict dominance**: if `ordAt α x < ordAt α y` then the sum has the
order of `x` (the smaller). -/
lemma ordAt_add_of_lt (α : K) {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ordAt α x < ordAt α y) : ordAt α (x + y) = ordAt α x := by
  have hnumx : x.num ≠ 0 := RatFunc.num_ne_zero hx
  have hnumy : y.num ≠ 0 := RatFunc.num_ne_zero hy
  have hdx : x.denom ≠ 0 := RatFunc.denom_ne_zero x
  have hdy : y.denom ≠ 0 := RatFunc.denom_ne_zero y
  have hxy0 : x + y ≠ 0 := by
    intro h0
    have hyx : y = -x := eq_neg_of_add_eq_zero_right h0
    rw [hyx, ordAt_neg] at h
    exact absurd h (lt_irrefl _)
  have hnumxy : (x + y).num ≠ 0 := RatFunc.num_ne_zero hxy0
  have e1 : Polynomial.rootMultiplicity α (x.num * y.denom)
      = Polynomial.rootMultiplicity α x.num + Polynomial.rootMultiplicity α y.denom :=
    Polynomial.rootMultiplicity_mul (mul_ne_zero hnumx hdy)
  have e2 : Polynomial.rootMultiplicity α (x.denom * y.num)
      = Polynomial.rootMultiplicity α x.denom + Polynomial.rootMultiplicity α y.num :=
    Polynomial.rootMultiplicity_mul (mul_ne_zero hdx hnumy)
  have e3 : Polynomial.rootMultiplicity α (x.denom * y.denom)
      = Polynomial.rootMultiplicity α x.denom + Polynomial.rootMultiplicity α y.denom :=
    Polynomial.rootMultiplicity_mul (mul_ne_zero hdx hdy)
  have hstrict : Polynomial.rootMultiplicity α (x.num * y.denom)
      < Polynomial.rootMultiplicity α (x.denom * y.num) := by
    rw [e1, e2]
    have hZ : ((Polynomial.rootMultiplicity α x.num : ℕ) : ℤ)
        + ((Polynomial.rootMultiplicity α y.denom : ℕ) : ℤ)
        < ((Polynomial.rootMultiplicity α x.denom + Polynomial.rootMultiplicity α y.num : ℕ) : ℤ) := by
      rw [Nat.cast_add]
      rw [ordAt, ordAt] at h
      linarith
    exact_mod_cast hZ
  have hdom := Commons.Algebra.Polynomial.rootMultiplicity_add_eq_of_lt
    (α := α) (p := x.num * y.denom) (q := x.denom * y.num) (mul_ne_zero hnumx hdy) hstrict
  have hA0 : x.num * y.denom + x.denom * y.num ≠ 0 := by
    intro h0
    exact (mul_ne_zero hnumxy (mul_ne_zero hdx hdy))
      (by rw [RatFunc.num_denom_add, h0, zero_mul])
  have hmain : Polynomial.rootMultiplicity α ((x + y).num)
      + (Polynomial.rootMultiplicity α x.denom + Polynomial.rootMultiplicity α y.denom)
      = Polynomial.rootMultiplicity α (x.num * y.denom + x.denom * y.num)
      + Polynomial.rootMultiplicity α ((x + y).denom) := by
    have hh := congrArg (Polynomial.rootMultiplicity α) (RatFunc.num_denom_add x y)
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hnumxy (mul_ne_zero hdx hdy)),
      Polynomial.rootMultiplicity_mul (mul_ne_zero hA0 (RatFunc.denom_ne_zero (x + y))),
      e3] at hh
    exact hh
  have hmain' : Polynomial.rootMultiplicity α ((x + y).num) + Polynomial.rootMultiplicity α x.denom
      = Polynomial.rootMultiplicity α x.num + Polynomial.rootMultiplicity α ((x + y).denom) := by
    have hh := hmain
    rw [hdom, e1] at hh
    omega
  simp only [ordAt]
  have hAZ : ((Polynomial.rootMultiplicity α ((x + y).num) : ℕ) : ℤ)
      + ((Polynomial.rootMultiplicity α x.denom : ℕ) : ℤ)
      = ((Polynomial.rootMultiplicity α x.num : ℕ) : ℤ)
      + ((Polynomial.rootMultiplicity α ((x + y).denom) : ℕ) : ℤ) := by
    exact_mod_cast hmain'
  linarith

end Submission.CDT
