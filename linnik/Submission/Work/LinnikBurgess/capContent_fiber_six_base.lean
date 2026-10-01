import Mathlib

/-!
# Foundations for `capContent_fiber_six`

This module collects the elementary polynomial and `p`-adic facts used by the proof of
`Work.LinnikBurgess.capContent_fiber_six`, which bounds the number of integers `y < p^M` with
`p^A ∣ Q(y)`, `ord_p Q'(y) = ν ≥ 1`, `p ∤ Q''(y)`.
-/

namespace Work.LinnikBurgess

open Polynomial

/-- **Divided-difference identity for integer polynomials.**
For `P : ℤ[X]` and integers `a, b` the difference `P.eval a - P.eval b` is divisible by `a - b`. -/
theorem int_dividedDiff (P : Polynomial ℤ) (a b : ℤ) :
    ∃ E : ℤ, P.eval a - P.eval b = (a - b) * E := by
  have hroot : (P - Polynomial.C (P.eval b)).IsRoot b := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C, sub_self]
  obtain ⟨F, hF⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  refine ⟨F.eval a, ?_⟩
  have h1 : (P - Polynomial.C (P.eval b)).eval a = (a - b) * F.eval a := by
    rw [hF, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Polynomial.eval_sub, Polynomial.eval_C] at h1
  exact h1

/-- **Second-order Taylor expansion of an integer polynomial.**
For `Q : ℤ[X]` and an integer `b` there is a polynomial `H : ℤ[X]` with
`Q.eval a = Q.eval b + (a - b) * Q'(b) + (a - b)^2 * H.eval a` for every integer `a`, and with
`2 * H.eval b = Q''.eval b`. -/
theorem taylor2_expansion (Q : Polynomial ℤ) (b : ℤ) :
    ∃ H : Polynomial ℤ,
      (∀ a : ℤ, Q.eval a = Q.eval b + (a - b) * Q.derivative.eval b
          + (a - b) ^ 2 * H.eval a) ∧
      2 * H.eval b = Q.derivative.derivative.eval b := by
  have hroot1 : (Q - Polynomial.C (Q.eval b)).IsRoot b := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C, sub_self]
  obtain ⟨G, hG⟩ := Polynomial.dvd_iff_isRoot.mpr hroot1
  -- `G.eval b = Q'.eval b`
  have hGeval : G.eval b = Q.derivative.eval b := by
    have hd := congrArg Polynomial.derivative hG
    simp only [Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.derivative_mul,
        Polynomial.derivative_sub, Polynomial.derivative_X, sub_zero, zero_mul, one_mul,
        mul_one, add_zero, zero_add] at hd
    have h2 := congrArg (fun R : Polynomial ℤ => R.eval b) hd
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, sub_self, zero_mul, add_zero] at h2
    exact h2.symm
  have hroot2 : (G - Polynomial.C (G.eval b)).IsRoot b := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_C, sub_self]
  obtain ⟨H, hH⟩ := Polynomial.dvd_iff_isRoot.mpr hroot2
  refine ⟨H, ?_, ?_⟩
  · intro a
    have hGa : Q.eval a - Q.eval b = (a - b) * G.eval a := by
      have h2 := congrArg (fun R : Polynomial ℤ => R.eval a) hG
      simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
        at h2
      exact h2
    have hHa : G.eval a - G.eval b = (a - b) * H.eval a := by
      have h2 := congrArg (fun R : Polynomial ℤ => R.eval a) hH
      simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
        at h2
      exact h2
    rw [hGeval] at hHa
    have hGae : G.eval a = Q.derivative.eval b + (a - b) * H.eval a := by linarith [hHa]
    rw [hGae] at hGa
    have hlin : Q.eval a
        = Q.eval b + (a - b) * (Q.derivative.eval b + (a - b) * H.eval a) := by
      linarith [hGa]
    rw [hlin]; ring
  · -- differentiate `G - C(G.eval b) = (X - C b) * H` twice
    have hdG := congrArg Polynomial.derivative hG
    simp only [Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.derivative_mul,
        Polynomial.derivative_sub, Polynomial.derivative_X, sub_zero, zero_mul, one_mul,
        mul_one, add_zero, zero_add] at hdG
    -- hdG : Q' = G + (X - C b) * G'
    have hdG2 := congrArg Polynomial.derivative hdG
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_sub,
        Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, zero_mul, one_mul,
        mul_one, add_zero, zero_add] at hdG2
    have hev := congrArg (fun R : Polynomial ℤ => R.eval b) hdG2
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, sub_self, zero_mul, add_zero] at hev
    -- hev : Q''.eval b = G'.eval b + G'.eval b
    have hdH := congrArg Polynomial.derivative hH
    simp only [Polynomial.derivative_sub, Polynomial.derivative_C, Polynomial.derivative_mul,
        Polynomial.derivative_sub, Polynomial.derivative_X, sub_zero, zero_mul, one_mul,
        mul_one, add_zero, zero_add] at hdH
    have hdHev := congrArg (fun R : Polynomial ℤ => R.eval b) hdH
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, sub_self, zero_mul, add_zero] at hdHev
    -- hdHev : G'.eval b = H.eval b
    rw [hdHev] at hev
    linarith [hev]

/-- The `p`-adic valuation of an integer is its `p`-adic valuation as a rational. -/
@[simp] theorem padicValRat_intCast {p : ℕ} (z : ℤ) :
    padicValRat p (z : ℚ) = (padicValNat p z.natAbs : ℤ) := by
  rw [padicValRat.of_int]; rfl

/-- **Additivity with strict inequality.** If `ord_p x < ord_p z` then `ord_p (x + z) = ord_p x`
(provided `x + z ≠ 0`). -/
theorem int_padicVal_add_eq_left {p : ℕ} [Fact p.Prime] {x z : ℤ}
    (hne : x + z ≠ 0) (hx : x ≠ 0) (hz : z ≠ 0)
    (hlt : padicValNat p x.natAbs < padicValNat p z.natAbs) :
    padicValNat p (x + z).natAbs = padicValNat p x.natAbs := by
  have h1 : padicValRat p ((x : ℚ)) < padicValRat p ((z : ℚ)) := by
    rw [padicValRat_intCast, padicValRat_intCast]; exact_mod_cast hlt
  have hqxz : ((x : ℚ)) + ((z : ℚ)) ≠ 0 := by
    have h : ((x : ℚ)) + ((z : ℚ)) = (((x + z : ℤ)) : ℚ) := by push_cast; ring
    rw [h]; exact_mod_cast hne
  have h2 : padicValRat p (((x : ℚ)) + ((z : ℚ))) = padicValRat p ((x : ℚ)) :=
    padicValRat.add_eq_of_lt hqxz (by exact_mod_cast hx) (by exact_mod_cast hz) h1
  have h3 : ((x : ℚ)) + ((z : ℚ)) = (((x + z : ℤ)) : ℚ) := by push_cast; ring
  rw [h3, padicValRat_intCast, padicValRat_intCast] at h2
  exact_mod_cast h2

/-- From `ord_p z = k`, `p ^ k` divides `z`. -/
theorem int_dvd_of_padicValNat_natAbs_eq {p : ℕ} {z : ℤ} {k : ℕ}
    (h : padicValNat p z.natAbs = k) : (((p ^ k : ℕ) : ℤ)) ∣ z := by
  have h1 : p ^ k ∣ z.natAbs := by rw [← h]; exact pow_padicValNat_dvd
  exact Int.natAbs_dvd_natAbs.mp (by simpa using h1)

/-- From `ord_p z = k` with `z ≠ 0`, `p ^ (k+1)` does **not** divide `z`. -/
theorem int_not_dvd_succ_of_padicValNat_natAbs_eq {p : ℕ} [Fact p.Prime] {z : ℤ} {k : ℕ}
    (hz : z ≠ 0) (h : padicValNat p z.natAbs = k) :
    ¬ (((p ^ (k + 1) : ℕ) : ℤ)) ∣ z := by
  intro hd
  have hdz : p ^ (k + 1) ∣ z.natAbs := Int.natAbs_dvd_natAbs.mpr (by simpa using hd)
  have hz' : z.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using hz
  have hcon := pow_succ_padicValNat_not_dvd (p := p) hz'
  rw [h] at hcon
  exact hcon hdz

/-- `ord_p z = k` with `k ≥ 1` forces `z ≠ 0` when `p` is prime. -/
theorem int_ne_zero_of_padicValNat_natAbs_eq {p : ℕ} {z : ℤ} {k : ℕ} (hk : 1 ≤ k)
    (h : padicValNat p z.natAbs = k) : z ≠ 0 := by
  intro hz
  rw [hz, Int.natAbs_zero] at h
  have h0 : padicValNat p 0 = 0 := padicValNat.zero
  omega

end Work.LinnikBurgess
