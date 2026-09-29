import Mathlib
import Submission.CDT.RatFuncDeriv
import Submission.CDT.RatFuncOrder
import Submission.CDT.RatFuncConstants
import Submission.Commons.Algebra.Polynomial.rootMultiplicity_derivative_num
import Submission.Commons.Algebra.Polynomial.derivative_mul_sub_eq_zero_of_isCoprime
import Submission.Commons.Algebra.Polynomial.exists_rootMultiplicity_pos_of_natDegree_ne_zero

/-!
# The order of vanishing of the derivative of a rational function

The ledger's "next layer" on top of `Submission.CDT.RatFuncDeriv` (the derivation `dRat` of `K(X)`)
and `Submission.CDT.RatFuncOrder` (the valuation `ordAt α`):

* **`ordAt_dRat_eq_sub_one`** — at a point where `f` has a zero or a pole, the derivative drops
  the order of vanishing by exactly one: `ordAt α (dRat f) = ordAt α f - 1` whenever
  `ordAt α f ≠ 0`;
* **`ordAt_dRat_ne_neg_one`** — **`dRat g` never has a simple pole**: for every rational function
  `g` and every `α`, `ordAt α (dRat g) ≠ -1`.  This is the "no simple pole" phenomenon in the form
  needed for the function-field Lindemann–Weierstrass theorem: the *logarithmic* derivative
  `(dRat f)/f` does have a simple pole (`ordAt α ((dRat f)/f) = -1` at every zero or pole of `f`,
  `ordAt_dRat_div_self`), so it can never be the derivative of a rational function;
* **`exists_ordAt_ne_zero_of_dRat_ne_zero`** — a rational function with `dRat f ≠ 0` (i.e. a
  nonconstant rational function, over a field in which every nonconstant polynomial has a root)
  has a zero or a pole.

The local input is the commons lemma
`Commons.Algebra.Polynomial.rootMultiplicity_derivative_num`: for coprime `u, v` with
`rootMultiplicity α u = 0` and `1 ≤ rootMultiplicity α v`, the quotient-rule numerator
`u' * v - u * v'` has root multiplicity exactly `rootMultiplicity α v - 1` at `α`.  Applied in the
two orientations — to `(u, v)` at a pole of `f = u/v`, to `(v, u)` at a zero — it gives both
statements above.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K]

/-- `dRat` on the canonical numerator/denominator representative of `f`. -/
theorem dRat_eq_div (f : RatFunc K) :
    dRat f = algebraMap (Polynomial K) (RatFunc K)
        (f.num.derivative * f.denom - f.num * f.denom.derivative)
      / (algebraMap (Polynomial K) (RatFunc K) f.denom) ^ 2 := by
  conv_lhs => rw [num_denom_eq f]
  exact dRat_div f.num f.denom

lemma rootMultiplicity_neg_eq (α : K) (p : Polynomial K) :
    rootMultiplicity α (-p) = rootMultiplicity α p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · have h : (-p) = C (-1 : K) * p := by simp
    rw [h, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (by norm_num)) hp),
      rootMultiplicity_C, zero_add]

/-- Coprimality rules out a common root. -/
lemma rootMultiplicity_eq_zero_of_isCoprime {u v : Polynomial K} (hcop : IsCoprime u v) {α : K}
    (hv : (X - C α) ∣ v) : rootMultiplicity α u = 0 := by
  refine rootMultiplicity_eq_zero ?_
  intro hroot
  exact not_isUnit_X_sub_C α (hcop.isUnit_of_dvd' (dvd_iff_isRoot.mpr hroot) hv)

/-- A root is a root of positive multiplicity. -/
lemma one_le_rootMultiplicity_of_dvd {v : Polynomial K} (hv : v ≠ 0) {α : K}
    (h : (X - C α) ∣ v) : 1 ≤ rootMultiplicity α v := by
  rw [le_rootMultiplicity_iff hv]
  simpa using h

section CharZero

variable [CharZero K]

/-- **`dRat` lowers the order of vanishing by exactly one** at a zero or a pole:
if `ordAt α f ≠ 0` then `ordAt α (dRat f) = ordAt α f - 1`. -/
theorem ordAt_dRat_eq_sub_one (f : RatFunc K) (α : K) (hα : ordAt α f ≠ 0) :
    ordAt α (dRat f) = ordAt α f - 1 := by
  have hv : f.denom ≠ 0 := RatFunc.denom_ne_zero f
  have hcop : IsCoprime f.num f.denom := RatFunc.isCoprime_num_denom f
  -- the quotient-rule numerator does not vanish: otherwise `f` would be constant
  have hN : f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := by
    intro h0
    obtain ⟨hu0, hv0⟩ := Commons.Algebra.Polynomial.derivative_mul_sub_eq_zero_of_isCoprime _ _ hcop h0
    have hnum0 : rootMultiplicity α f.num = 0 := by
      rw [eq_C_of_natDegree_eq_zero (derivative_eq_zero.mp hu0), rootMultiplicity_C]
    have hden0 : rootMultiplicity α f.denom = 0 := by
      rw [eq_C_of_natDegree_eq_zero (derivative_eq_zero.mp hv0), rootMultiplicity_C]
    exact hα (by rw [ordAt, hnum0, hden0]; norm_num)
  -- the raw value of `ordAt α (dRat f)`
  have hval : ordAt α (dRat f)
      = (rootMultiplicity α (f.num.derivative * f.denom - f.num * f.denom.derivative) : ℤ)
        - 2 * (rootMultiplicity α f.denom : ℤ) := by
    rw [dRat_eq_div]
    rw [ordAt_div α (RatFunc.algebraMap_ne_zero hN)
      (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero hv))]
    rw [ordAt_algebraMap, ordAt_pow, ordAt_algebraMap]
    ring
  have hordf : ordAt α f
      = (rootMultiplicity α f.num : ℤ) - (rootMultiplicity α f.denom : ℤ) := rfl
  by_cases hden : rootMultiplicity α f.denom = 0
  · -- `α` is a zero of `f`: apply the multiplicity lemma to the swapped pair
    have hnum : 1 ≤ rootMultiplicity α f.num := by
      have h1 : (rootMultiplicity α f.num : ℤ) ≠ 0 := by
        intro h
        exact hα (by rw [ordAt, hden, h]; norm_num)
      omega
    have hswap := Commons.Algebra.Polynomial.rootMultiplicity_derivative_num
      f.denom f.num hcop.symm α hden hnum
    have hNeq : f.num.derivative * f.denom - f.num * f.denom.derivative
        = -(f.denom.derivative * f.num - f.denom * f.num.derivative) := by ring
    rw [hval, hNeq, rootMultiplicity_neg_eq, hswap, hordf, hden]
    have hcast : ((rootMultiplicity α f.num - 1 : ℕ) : ℤ) = (rootMultiplicity α f.num : ℤ) - 1 :=
      Nat.cast_sub hnum
    rw [hcast]; ring
  · -- `α` is a pole of `f`: apply the multiplicity lemma to `(num, denom)`
    have hden1 : 1 ≤ rootMultiplicity α f.denom := by omega
    have hnum0 : rootMultiplicity α f.num = 0 :=
      rootMultiplicity_eq_zero_of_isCoprime hcop
        (by simpa using (le_rootMultiplicity_iff hv).mp hden1)
    have hmain := Commons.Algebra.Polynomial.rootMultiplicity_derivative_num
      f.num f.denom hcop α hnum0 hden1
    rw [hval, hmain, hordf, hnum0]
    have hcast : ((rootMultiplicity α f.denom - 1 : ℕ) : ℤ) = (rootMultiplicity α f.denom : ℤ) - 1 :=
      Nat.cast_sub hden1
    rw [hcast]; ring

/-- **`dRat g` has no simple pole**: `ordAt α (dRat g) ≠ -1` for every `g` and every `α`. -/
theorem ordAt_dRat_ne_neg_one (α : K) (g : RatFunc K) : ordAt α (dRat g) ≠ -1 := by
  have hcop : IsCoprime g.num g.denom := RatFunc.isCoprime_num_denom g
  have hv : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  rcases eq_or_ne (g.num.derivative * g.denom - g.num * g.denom.derivative) 0 with hN | hN
  · rw [dRat_eq_div, hN, map_zero, zero_div, ordAt_zero]; norm_num
  · have hval : ordAt α (dRat g)
        = (rootMultiplicity α (g.num.derivative * g.denom - g.num * g.denom.derivative) : ℤ)
          - 2 * (rootMultiplicity α g.denom : ℤ) := by
      rw [dRat_eq_div]
      rw [ordAt_div α (RatFunc.algebraMap_ne_zero hN)
        (pow_ne_zero 2 (RatFunc.algebraMap_ne_zero hv))]
      rw [ordAt_algebraMap, ordAt_pow, ordAt_algebraMap]
      ring
    by_cases hden : rootMultiplicity α g.denom = 0
    · rw [hval, hden, Nat.cast_zero, mul_zero, sub_zero]
      have hnn : (0 : ℤ) ≤ (rootMultiplicity α
          (g.num.derivative * g.denom - g.num * g.denom.derivative) : ℤ) :=
        Int.natCast_nonneg _
      omega
    · have hden1 : 1 ≤ rootMultiplicity α g.denom := by omega
      have hnum0 : rootMultiplicity α g.num = 0 :=
        rootMultiplicity_eq_zero_of_isCoprime hcop
          (by simpa using (le_rootMultiplicity_iff hv).mp hden1)
      have hmain := Commons.Algebra.Polynomial.rootMultiplicity_derivative_num
        g.num g.denom hcop α hnum0 hden1
      rw [hval, hmain]
      have hcast : ((rootMultiplicity α g.denom - 1 : ℕ) : ℤ)
          = (rootMultiplicity α g.denom : ℤ) - 1 := Nat.cast_sub hden1
      rw [hcast]
      have h1 : (1 : ℤ) ≤ (rootMultiplicity α g.denom : ℤ) := by exact_mod_cast hden1
      omega

/-- **The logarithmic derivative has a simple pole**: at every zero or pole of `f`,
`ordAt α ((dRat f) / f) = -1`. -/
theorem ordAt_dRat_div_self (f : RatFunc K) (α : K) (hα : ordAt α f ≠ 0) :
    ordAt α (dRat f / f) = -1 := by
  have hf0 : f ≠ 0 := fun h => hα (by rw [h]; simp)
  have hd : dRat f ≠ 0 := by
    intro h
    obtain ⟨c, hc⟩ := exists_const_of_dRat_eq_zero h
    exact hα (by rw [hc, ← am_C', ordAt_algebraMap, rootMultiplicity_C]; norm_num)
  rw [ordAt_div α hd hf0, ordAt_dRat_eq_sub_one f α hα]
  ring

end CharZero

/-- A rational function whose derivative does not vanish has a zero or a pole (over a field in
which every nonconstant polynomial has a root; e.g. an algebraically closed field). -/
theorem exists_ordAt_ne_zero_of_dRat_ne_zero [IsAlgClosed K] (f : RatFunc K)
    (hf : dRat f ≠ 0) : ∃ α : K, ordAt α f ≠ 0 := by
  have hf0 : f ≠ 0 := fun h => hf (by rw [h, dRat_zero])
  have hu : f.num ≠ 0 := RatFunc.num_ne_zero hf0
  have hcop : IsCoprime f.num f.denom := RatFunc.isCoprime_num_denom f
  have hN : f.num.derivative * f.denom - f.num * f.denom.derivative ≠ 0 := by
    intro h0
    refine hf ?_
    rw [dRat_eq_div, h0, map_zero, zero_div]
  by_cases hu0 : f.num.natDegree = 0
  · by_cases hv0 : f.denom.natDegree = 0
    · exact absurd (by
        rw [eq_C_of_natDegree_eq_zero hu0, eq_C_of_natDegree_eq_zero hv0, derivative_C,
          derivative_C]; ring) hN
    · obtain ⟨α, hα⟩ := Commons.Algebra.Polynomial.exists_rootMultiplicity_pos_of_natDegree_ne_zero f.denom hv0
      refine ⟨α, ?_⟩
      have hnum : rootMultiplicity α f.num = 0 := by
        rw [eq_C_of_natDegree_eq_zero hu0, rootMultiplicity_C]
      show ((rootMultiplicity α f.num : ℤ) - (rootMultiplicity α f.denom : ℤ)) ≠ 0
      rw [hnum]
      have h1 : (1 : ℤ) ≤ (rootMultiplicity α f.denom : ℤ) := by exact_mod_cast hα
      omega
  · obtain ⟨α, hα⟩ := Commons.Algebra.Polynomial.exists_rootMultiplicity_pos_of_natDegree_ne_zero f.num hu0
    refine ⟨α, ?_⟩
    have hden : rootMultiplicity α f.denom = 0 :=
      rootMultiplicity_eq_zero_of_isCoprime hcop.symm (by
        simpa using (le_rootMultiplicity_iff hu).mp hα)
    show ((rootMultiplicity α f.num : ℤ) - (rootMultiplicity α f.denom : ℤ)) ≠ 0
    rw [hden]
    have h1 : (1 : ℤ) ≤ (rootMultiplicity α f.num : ℤ) := by exact_mod_cast hα
    omega

end Submission.CDT
