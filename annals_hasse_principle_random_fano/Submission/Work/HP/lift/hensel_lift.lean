import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.density_aux
import Submission.Work.HP.lift.line_setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Multivariate Hensel lifting in the singular case

This file proves `Work.HP.lift.hensel_lift` (the node of the density argument that replaces
Poonen–Voloch at the bad primes).

The mathematical content is the classical singular Hensel lemma: if `x` is a primitive zero of
the form `f_a` modulo `p^(2e+1)` and the gradient of `f_a` at `x` has `p`-adic valuation exactly
`e`, then `f_a` has a primitive zero modulo `p^R` for every `R ≥ 2e+1`.

The proof reduces the multivariate statement to a univariate one, and then runs Newton's
iteration on that univariate polynomial:

* `linePoly d n a x i` (`Submission/Work/HP/lift/line_setup.lean`) is the restriction of `f_a`
  to the affine line `u ↦ x + u·e_i`, a polynomial in `u` with integer coefficients;
  `linePoly_eval` and `linePoly_deriv` compute its value and its derivative at `0` (the latter
  is the `i`-th partial derivative of `f_a` at `x`).
* `poly_hensel` is univariate Hensel lifting: `W(0) ≡ 0 mod p^(2e+1)` and
  `v_p(W'(0)) = e` imply a root of `W` modulo `p^R` for every `R ≥ 2e+1`, congruent to `0`
  modulo `p^(e+1)`.
* Taking the direction `i` with `v_p(∂_i f_a(x)) = e` (which exists by hypothesis) and
  `W = linePoly d n a x i`, the root `u` produced by `poly_hensel` gives the vector
  `x + u·e_i`, which is primitive mod `p` because `p | u`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP.lift

/-! ## Products over the coordinates of a point -/

/-- The coordinate formula for the shifted point `x + u·e_i`. -/
theorem add_single_apply (n : ℕ) (x : Fin (n + 1) → ℤ) (i : Fin (n + 1)) (u : ℤ)
    (j : Fin (n + 1)) :
    (x + Pi.single i u : Fin (n + 1) → ℤ) j = (if j = i then x i + u else x j) := by
  by_cases h : j = i
  · rw [h, Pi.add_apply, Pi.single_eq_same, if_pos rfl]
  · rw [Pi.add_apply, Pi.single_eq_of_ne h, add_zero, if_neg h]

/-- A product over all coordinates, split at `i`, when coordinate `i` has been set to `v`. -/
theorem prod_univ_ite (n : ℕ) (x : Fin (n + 1) → ℤ) (i : Fin (n + 1)) (v : ℤ)
    (k : Fin (n + 1) → ℕ) :
    (∏ j, (if j = i then v else x j) ^ k j)
      = v ^ k i * ∏ j ∈ Finset.univ.erase i, x j ^ k j := by
  rw [← Finset.mul_prod_erase (Finset.univ) (fun j => (if j = i then v else x j) ^ k j)
    (a := i) (Finset.mem_univ i)]
  congr 1
  · rw [if_pos rfl]
  · exact Finset.prod_congr rfl fun j hj => by
      rw [Finset.mem_erase] at hj
      rw [if_neg hj.1]

/-- Splitting a product over all coordinates at `i`, with the exponent reduced by one at `i`. -/
theorem prod_univ_sub_single (n : ℕ) (x : Fin (n + 1) → ℤ) (i : Fin (n + 1))
    (k : Fin (n + 1) → ℕ) :
    (∏ j, x j ^ (k j - if j = i then 1 else 0))
      = x i ^ (k i - 1) * ∏ j ∈ Finset.univ.erase i, x j ^ k j := by
  rw [← Finset.mul_prod_erase (Finset.univ) (fun j => x j ^ (k j - if j = i then 1 else 0))
    (a := i) (Finset.mem_univ i)]
  congr 1
  · rw [if_pos rfl]
  · exact Finset.prod_congr rfl fun j hj => by
      rw [Finset.mem_erase] at hj
      rw [if_neg hj.1, Nat.sub_zero]

/-- A product of powers of the constants `C (x j)` is `C` applied to the corresponding product. -/
theorem prod_C_pow_eq_C_prod (n : ℕ) (x : Fin (n + 1) → ℤ) (s : Finset (Fin (n + 1)))
    (k : Fin (n + 1) → ℕ) :
    (∏ j ∈ s, (Polynomial.C (x j)) ^ (k j)) = Polynomial.C (∏ j ∈ s, x j ^ (k j)) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      calc (∏ j ∈ insert a s, (Polynomial.C (x j)) ^ (k j))
          = (Polynomial.C (x a)) ^ (k a) * ∏ j ∈ s, (Polynomial.C (x j)) ^ (k j) := by
            rw [Finset.prod_insert ha]
        _ = (Polynomial.C (x a)) ^ (k a) * Polynomial.C (∏ j ∈ s, x j ^ (k j)) := by rw [ih]
        _ = Polynomial.C (x a ^ k a) * Polynomial.C (∏ j ∈ s, x j ^ (k j)) := by
            rw [Polynomial.C_pow]
        _ = Polynomial.C (x a ^ k a * ∏ j ∈ s, x j ^ (k j)) := by rw [Polynomial.C_mul]
        _ = Polynomial.C (∏ j ∈ insert a s, x j ^ (k j)) := by rw [Finset.prod_insert ha]

/-! ## The line restriction and its derivative -/

/-- The univariate polynomial `linePoly d n a x i` evaluates at `u` to the value of the form
`f_a` at the point `x + u·e_i`. -/
theorem linePoly_eval (d n : ℕ) (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) (i : Fin (n + 1))
    (u : ℤ) : (linePoly d n a x i).eval u = formEval d n a (x + Pi.single i u) := by
  rw [linePoly, formEval, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_prod, veronese]
  have hprod : (∏ j, (x + Pi.single i u : Fin (n + 1) → ℤ) j ^ (m.1 j : ℕ))
      = ∏ j, (if j = i then x i + u else x j) ^ (m.1 j : ℕ) :=
    Finset.prod_congr rfl fun j _ => by rw [add_single_apply]
  rw [hprod, prod_univ_ite]
  push_cast
  ring

/-- The evaluation at `0` of the derivative of one summand of `linePoly`. -/
theorem eval_zero_derivative_term (c y q : ℤ) (k : ℕ) :
    (Polynomial.derivative (Polynomial.C c * (Polynomial.C y + Polynomial.X) ^ k
      * Polynomial.C q)).eval 0 = c * (k : ℤ) * y ^ (k - 1) * q := by
  have hd : (Polynomial.C c * (Polynomial.C y + Polynomial.X) ^ k * Polynomial.C q).derivative
      = Polynomial.C c * (Polynomial.C (k : ℤ) * (Polynomial.C y + Polynomial.X) ^ (k - 1))
        * Polynomial.C q := by
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_pow,
      Polynomial.derivative_add, Polynomial.derivative_X]
    ring
  rw [hd]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, add_zero]
  ring

/-- The derivative at `0` of `linePoly d n a x i` is the `i`-th partial derivative of `f_a`
at `x`. -/
theorem linePoly_deriv (d n : ℕ) (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    (linePoly d n a x i).derivative.eval 0 = pderivEval d n a i x := by
  simp only [linePoly, pderivEval]
  rw [Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [prod_C_pow_eq_C_prod n x (Finset.univ.erase i) (fun j => (m.1 j : ℕ)),
    eval_zero_derivative_term, prod_univ_sub_single]
  ring

/-! ## Univariate Hensel lifting in the singular case -/

/-- A linear congruence modulo `p` with a unit coefficient is solvable. -/
theorem exists_mul_add_dvd (p : ℕ) (hp : p.Prime) (g c : ℤ) (hg : ¬ (p : ℤ) ∣ g) :
    ∃ δ : ℤ, (p : ℤ) ∣ c + δ * g := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hg0 : (g : ZMod p) ≠ 0 := fun h => hg ((ZMod.intCast_zmod_eq_zero_iff_dvd g p).mp h)
  set t : ZMod p := -(c : ZMod p) * (g : ZMod p)⁻¹ with ht
  refine ⟨(t.val : ℤ), ?_⟩
  have h1 : (((t.val : ℤ)) : ZMod p) = t := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val t
  have h2 : ((c + (t.val : ℤ) * g : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_add, Int.cast_mul, h1, ht, mul_assoc, inv_mul_cancel₀ hg0, mul_one,
      add_neg_cancel]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h2

/-- One Newton step of the singular lifting: from a root of `W` modulo `p^s` (with `s ≥ 2e+1`)
that is divisible by `p^(e+1)` and whose derivative has valuation exactly `e`, produce a root
modulo `p^(s+1)` of the same shape. -/
theorem lift_step (W : Polynomial ℤ) (p : ℕ) (hp : p.Prime) (e s : ℕ) (g0 : ℤ)
    (hg0 : Polynomial.eval 0 W.derivative = (p : ℤ) ^ e * g0)
    (hg0' : ¬ (p : ℤ) ∣ g0)
    (u : ℤ) (hs : 2 * e + 1 ≤ s) (hu : (p : ℤ) ^ (e + 1) ∣ u)
    (hWu : (p : ℤ) ^ s ∣ Polynomial.eval u W) :
    ∃ u' : ℤ, (p : ℤ) ^ (e + 1) ∣ u' ∧ (p : ℤ) ^ (s + 1) ∣ Polynomial.eval u' W := by
  obtain ⟨z, hz⟩ := dvd_eval_derivative_sub W 0 u
  rw [zero_add] at hz
  obtain ⟨t, ht⟩ := hu
  obtain ⟨c, hc⟩ := hWu
  have hgu : ∃ g : ℤ, Polynomial.eval u W.derivative = (p : ℤ) ^ e * g ∧ ¬ (p : ℤ) ∣ g := by
    refine ⟨g0 + (p : ℤ) * (t * z), ?_, ?_⟩
    · have h1 : Polynomial.eval u W.derivative = Polynomial.eval 0 W.derivative + u * z := by
        linarith [hz]
      rw [h1, hg0, ht, pow_succ]
      ring
    · intro h
      exact hg0' (by
        have h2 : (p : ℤ) ∣ (p : ℤ) * (t * z) := dvd_mul_right _ _
        simpa using dvd_sub h h2)
  obtain ⟨g, hg_eq, hg_ndvd⟩ := hgu
  obtain ⟨δ, hδ⟩ := exists_mul_add_dvd p hp g c hg_ndvd
  have he1 : e + 1 ≤ s - e := by omega
  have he2 : s + 1 ≤ (s - e) * 2 := by omega
  have he3 : e ≤ s := by omega
  refine ⟨u + (p : ℤ) ^ (s - e) * δ, ?_, ?_⟩
  · rw [ht]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) he1) δ)
  · obtain ⟨q, hq⟩ := sq_dvd_eval_sub_eval_sub_mul_derivative W u ((p : ℤ) ^ (s - e) * δ)
    have hmain : Polynomial.eval (u + (p : ℤ) ^ (s - e) * δ) W =
        Polynomial.eval u W + (p : ℤ) ^ (s - e) * δ * Polynomial.eval u W.derivative
          + ((p : ℤ) ^ (s - e) * δ) ^ 2 * q := by
      linarith [hq]
    rw [hmain]
    refine dvd_add ?_ (dvd_mul_of_dvd_left ?_ q)
    · have hpow : (p : ℤ) ^ (s - e) * (p : ℤ) ^ e = (p : ℤ) ^ s := by
        rw [← pow_add, Nat.sub_add_cancel he3]
      have hsplit : Polynomial.eval u W + (p : ℤ) ^ (s - e) * δ * Polynomial.eval u W.derivative
          = (p : ℤ) ^ s * (c + δ * g) := by
        rw [hc, hg_eq]
        linear_combination (δ * g) * hpow
      rw [hsplit, pow_succ]
      exact mul_dvd_mul_left _ hδ
    · rw [mul_pow, ← pow_mul]
      exact dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) he2) (δ ^ 2)

/-- Univariate Hensel lifting in the singular case. -/
theorem poly_hensel (W : Polynomial ℤ) (p : ℕ) (hp : p.Prime) (e R : ℕ)
    (h0 : (p : ℤ) ^ (2 * e + 1) ∣ Polynomial.eval 0 W)
    (h1 : (p : ℤ) ^ e ∣ Polynomial.eval 0 W.derivative)
    (h2 : ¬ (p : ℤ) ^ (e + 1) ∣ Polynomial.eval 0 W.derivative)
    (hR : 2 * e + 1 ≤ R) :
    ∃ u : ℤ, (p : ℤ) ^ (e + 1) ∣ u ∧ (p : ℤ) ^ R ∣ Polynomial.eval u W := by
  obtain ⟨g0, hg0⟩ := h1
  have hg0' : ¬ (p : ℤ) ∣ g0 := by
    intro h
    apply h2
    obtain ⟨m, hm⟩ := h
    rw [hg0, hm, pow_succ]
    exact mul_dvd_mul_left _ (dvd_mul_right (p : ℤ) m)
  exact Nat.le_induction (m := 2 * e + 1)
    (P := fun s _ => ∃ u : ℤ, (p : ℤ) ^ (e + 1) ∣ u ∧ (p : ℤ) ^ s ∣ Polynomial.eval u W)
    ⟨0, dvd_zero _, h0⟩
    (fun s hs ih => by
      obtain ⟨u, hu1, hu2⟩ := ih
      exact lift_step W p hp e s g0 hg0 hg0' u hs hu1 hu2)
    R hR

/-! ## Multivariate Hensel lifting -/

/-- Multivariate Hensel lifting (singular case).  If `x` is a primitive zero of `f_a` modulo
`p^(2e+1)` and the gradient of `f_a` at `x` has `p`-adic valuation exactly `e` (all partial
derivatives divisible by `p^e`, one not divisible by `p^(e+1)`), then `a` has a primitive zero
modulo `p^R` for every `R ≥ 2e+1`.  With `e = 0`: a primitive zero of `f_a` mod `p` where the
gradient does not vanish identically mod `p` lifts to a primitive zero modulo `p^R` for all `R`. -/
theorem hensel_lift (d n : ℕ) (p : ℕ) (hp : p.Prime) (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ)
    (e R : ℕ) (hx : ∃ i, ¬ (p : ℤ) ∣ x i)
    (hzero : (p : ℤ) ^ (2 * e + 1) ∣ formEval d n a x)
    (he : ∀ i, (p : ℤ) ^ e ∣ pderivEval d n a i x)
    (he' : ∃ i, ¬ (p : ℤ) ^ (e + 1) ∣ pderivEval d n a i x)
    (hR : 2 * e + 1 ≤ R) :
    PrimModZero d n a p R := by
  obtain ⟨i0, hi0⟩ := he'
  have hxt : x + Pi.single i0 (0 : ℤ) = x := by rw [Pi.single_zero, add_zero]
  have hW0 : (linePoly d n a x i0).eval 0 = formEval d n a x := by rw [linePoly_eval, hxt]
  have hW1 : (linePoly d n a x i0).derivative.eval 0 = pderivEval d n a i0 x :=
    linePoly_deriv d n a x i0
  obtain ⟨u, hu1, hu2⟩ := poly_hensel (linePoly d n a x i0) p hp e R
    (by rw [hW0]; exact hzero) (by rw [hW1]; exact he i0) (by rw [hW1]; exact hi0) hR
  refine ⟨x + Pi.single i0 u, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hx
    by_cases hji : j = i0
    · rw [hji] at hj
      have hu : (p : ℤ) ∣ u := by
        have h1 : (p : ℤ) ∣ (p : ℤ) ^ (e + 1) := by
          simpa using pow_dvd_pow (p : ℤ) (Nat.succ_le_succ (Nat.zero_le e))
        exact dvd_trans h1 hu1
      refine ⟨i0, ?_⟩
      have h1 : (x + Pi.single i0 u : Fin (n + 1) → ℤ) i0 = x i0 + u := by
        rw [Pi.add_apply, Pi.single_eq_same]
      rw [h1]
      intro hd
      exact hj (by simpa using dvd_sub hd hu)
    · have h1 : (x + Pi.single i0 u : Fin (n + 1) → ℤ) j = x j := by
        rw [Pi.add_apply, Pi.single_eq_of_ne hji, add_zero]
      refine ⟨j, ?_⟩
      rw [h1]
      exact hj
  · rw [← linePoly_eval d n a x i0 u]
    exact hu2

end Work.HP.lift
