import Mathlib
import Submission.Work.A3.CSPoly

/-!
# The divided difference `polydiff`: evaluation, degree and leading coefficient

`Work.A3.polydiff g h` (defined in `Submission/Work/A3/CSPoly.lean`) is the divided difference
`(g(X + h) - g(X)) / h`, written with explicit integer coefficients so that no division in `ℤ[X]`
is needed:

`polydiff g h = ∑ i ∈ g.support, C (g.coeff i) * ∑ j ∈ range i, C ((i.choose j) * h ^ (i - j - 1)) * X ^ j`.

This file proves the three properties of it that the circle-method argument uses:

* `Work.A3.polydiff_spec` — the evaluation identity `(polydiff g h).eval t * h = g.eval (t + h) - g.eval t`
  (for all `t : ℤ`), together with `natDegree (polydiff g h) = e - 1` and
  `leadingCoeff (polydiff g h) = e * g.leadingCoeff`, where `e = g.natDegree ≥ 1` and `h ≠ 0`.

The route is uniform.  Multiplying the defining sum by `C h` clears the `h`-powers in the
denominators and gives, for each `i`, the binomial expansion of `(X + C h)^i - X^i`; summing over
`i ∈ g.support` and comparing with `g.comp (X + C h) - g = (g(X + h) - g)` gives the polynomial
identity `C h * polydiff g h = g.comp (X + C h) - g`, from which the evaluation identity follows by
evaluating at `t`.  The displayed expansion also computes the coefficients of `C h * polydiff g h`
directly, which yields the degree and the leading coefficient (using `h ≠ 0` to divide by `C h`).
-/

set_option autoImplicit false

namespace Work.A3

open Polynomial Finset

/-- The coefficient of a finite sum of polynomials is the sum of the coefficients. -/
lemma coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  rw [← Polynomial.lcoeff_apply, map_sum]
  simp [Polynomial.lcoeff_apply]

/-- The binomial expansion of `(X + C h) ^ i - X ^ i`, in the exact shape in which the defining sum
of `polydiff` presents it after multiplication by `C h`. -/
lemma sum_range_choose_mul_pow_mul_X (i : ℕ) (h : ℤ) :
    (∑ j ∈ Finset.range i, C ((i.choose j : ℤ) * h ^ (i - j)) * X ^ j : ℤ[X])
      = (X + C h) ^ i - X ^ i := by
  rw [add_pow]
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one]
  rw [add_sub_cancel_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [← C_eq_natCast, ← C_pow, C_mul]
  ring

/-- The defining sum of `polydiff g h`, multiplied by `C h`, written as a sum over the support of
`g` of the binomial expansions of `(X + C h)^i - X^i`. -/
lemma C_mul_polydiff_expand (g : ℤ[X]) (h : ℤ) :
    C h * polydiff g h
      = ∑ i ∈ g.support,
          C (g.coeff i) * ∑ j ∈ Finset.range i, C ((i.choose j : ℤ) * h ^ (i - j)) * X ^ j := by
  rw [polydiff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < i := Finset.mem_range.mp hj
  have hpow : h * ((i.choose j : ℤ) * h ^ (i - j - 1)) = (i.choose j : ℤ) * h ^ (i - j) := by
    have h1 : i - j - 1 + 1 = i - j := by omega
    rw [mul_comm h ((i.choose j : ℤ) * h ^ (i - j - 1)), mul_assoc, ← pow_succ, h1]
  have hC : C h * C ((i.choose j : ℤ) * h ^ (i - j - 1)) = C ((i.choose j : ℤ) * h ^ (i - j)) := by
    rw [← C_mul, hpow]
  calc C h * (C (g.coeff i) * (C ((i.choose j : ℤ) * h ^ (i - j - 1)) * X ^ j))
      = C (g.coeff i) * ((C h * C ((i.choose j : ℤ) * h ^ (i - j - 1))) * X ^ j) := by ring
    _ = C (g.coeff i) * (C ((i.choose j : ℤ) * h ^ (i - j)) * X ^ j) := by rw [hC]

/-- The polynomial identity behind the evaluation formula: multiplying the divided difference by `h`
recovers `g(X + h) - g(X)`. -/
lemma C_mul_polydiff_eq_comp_sub (g : ℤ[X]) (h : ℤ) :
    C h * polydiff g h = g.comp (X + C h) - g := by
  rw [C_mul_polydiff_expand]
  have hgc : g.comp (X + C h) = ∑ i ∈ g.support, C (g.coeff i) * (X + C h) ^ i := by
    rw [comp_eq_sum_left, Polynomial.sum]
  calc ∑ i ∈ g.support,
        C (g.coeff i) * ∑ j ∈ Finset.range i, C ((i.choose j : ℤ) * h ^ (i - j)) * X ^ j
      = ∑ i ∈ g.support, C (g.coeff i) * ((X + C h) ^ i - X ^ i) := by
        refine Finset.sum_congr rfl fun i _ => by rw [sum_range_choose_mul_pow_mul_X i h]
    _ = ∑ i ∈ g.support, (C (g.coeff i) * (X + C h) ^ i - C (g.coeff i) * X ^ i) := by
        refine Finset.sum_congr rfl fun i _ => by ring
    _ = (∑ i ∈ g.support, C (g.coeff i) * (X + C h) ^ i)
          - ∑ i ∈ g.support, C (g.coeff i) * X ^ i := Finset.sum_sub_distrib _ _
    _ = g.comp (X + C h) - g := by rw [hgc, ← as_sum_support_C_mul_X_pow g]

/-- The coefficients of `C h * polydiff g h`, read off from the expansion `C_mul_polydiff_expand`. -/
lemma coeff_C_mul_polydiff (g : ℤ[X]) (h : ℤ) (n : ℕ) :
    (C h * polydiff g h).coeff n
      = ∑ i ∈ g.support,
          g.coeff i * (if n < i then (i.choose n : ℤ) * h ^ (i - n) else 0) := by
  rw [C_mul_polydiff_expand, coeff_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_C_mul]
  congr 1
  rw [coeff_finset_sum]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

lemma polydiff_spec (g : Polynomial ℤ) (h : ℤ) {e : ℕ} (he : g.natDegree = e) (he1 : 1 ≤ e)
    (hh : h ≠ 0) :
    (∀ t : ℤ, (Work.A3.polydiff g h).eval t * h = g.eval (t + h) - g.eval t) ∧
    (Work.A3.polydiff g h).natDegree = e - 1 ∧
    (Work.A3.polydiff g h).leadingCoeff = (e : ℤ) * g.leadingCoeff := by
  have hg : g ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at he
    omega
  have hglc : g.leadingCoeff ≠ 0 := fun h0 => hg (Polynomial.leadingCoeff_eq_zero.mp h0)
  have hcoeff_e : g.coeff e = g.leadingCoeff := by
    rw [← he]
    exact Polynomial.coeff_natDegree
  -- degree bound from the vanishing of all coefficients of degree at least `e`
  have hle : (C h * polydiff g h).natDegree ≤ e - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_C_mul_polydiff]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi_le : i ≤ e := by
      rw [← he]
      exact le_natDegree_of_ne_zero (mem_support_iff.mp hi)
    simp only [if_neg (by omega : ¬ N < i), mul_zero]
  -- the top coefficient
  have hchoose : (e.choose (e - 1) : ℤ) = (e : ℤ) := by
    have hh3 := Nat.choose_succ_self_right (e - 1)
    rw [show e - 1 + 1 = e from by omega] at hh3
    exact_mod_cast hh3
  have hcoeff_top : (C h * polydiff g h).coeff (e - 1) = g.leadingCoeff * ((e : ℤ) * h) := by
    have hesupp : e ∈ g.support := mem_support_iff.mpr (by rw [hcoeff_e]; exact hglc)
    rw [coeff_C_mul_polydiff]
    have hterm : ∀ i ∈ g.support,
        g.coeff i * (if e - 1 < i then (i.choose (e - 1) : ℤ) * h ^ (i - (e - 1)) else 0)
          = if i = e then g.leadingCoeff * ((e : ℤ) * h) else 0 := by
      intro i hi
      by_cases hie : i = e
      · rw [hie,
          if_pos (by omega : e - 1 < e), show e - (e - 1) = 1 from by omega, pow_one, hchoose,
          hcoeff_e, if_pos rfl]
      · rw [if_neg hie]
        have hi_le : i ≤ e := by
          rw [← he]
          exact le_natDegree_of_ne_zero (mem_support_iff.mp hi)
        simp only [if_neg (by omega : ¬ e - 1 < i), mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos hesupp]
  have he_ne : (e : ℤ) ≠ 0 := by omega
  have hnat : (C h * polydiff g h).natDegree = e - 1 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle
      (by rw [hcoeff_top]; exact mul_ne_zero hglc (mul_ne_zero he_ne hh))
  have hdeg : (polydiff g h).natDegree = e - 1 := by
    have h1 := Polynomial.natDegree_C_mul (p := polydiff g h) hh
    rw [hnat] at h1
    exact h1.symm
  have hlc1 : (C h * polydiff g h).leadingCoeff = h * (polydiff g h).leadingCoeff := by
    simp only [Polynomial.leadingCoeff, Polynomial.coeff_C_mul, Polynomial.natDegree_C_mul hh]
  have hlc2 : (C h * polydiff g h).leadingCoeff = g.leadingCoeff * ((e : ℤ) * h) := by
    simp only [Polynomial.leadingCoeff, hnat, hcoeff_top]
  have hlc : (polydiff g h).leadingCoeff = (e : ℤ) * g.leadingCoeff := by
    refine mul_left_cancel₀ hh ?_
    rw [← hlc1, hlc2]
    ring
  refine ⟨?_, hdeg, hlc⟩
  intro t
  have h := congrArg (fun p : ℤ[X] => p.eval t) (C_mul_polydiff_eq_comp_sub g h)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X] at h
  rw [mul_comm]
  exact h

end Work.A3
