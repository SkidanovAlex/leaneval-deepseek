import Mathlib
import Submission.Work.LinnikBurgess.ddLevelDefs

/-!
# The level-`1` expansion of the product coordinate `Φ(w) = ∏(1+pA_l w)·∏(1+pC_l w)⁻¹`

For `A C : Fin 3 → ZMod (p^e)` and `w : ZMod (p^e)` the product coordinate admits the expansion

`Φ(w) = 1 + p·Δ₁·w + p²·E₂·w² + p³·E₃·w³ + p⁴·G(w)`

with `Δ₁ = ddDsum p e 1 A C`, `E₂ = ddE2 A C`, `E₃ = ddE3 A C` and `G` a polynomial over
`ZMod (p^e)`.

## Proof

Write `A(w) = ∏_l (1 + p A_l w) = 1 + p e₁(A) w + p² e₂(A) w² + p³ e₃(A) w³` (three factors) and
`D(w) = ∏_l (1 + p C_l w)`.  Clearing the denominator `D(w)` of `Φ(w) = A(w)/D(w)` reduces the
claim to the polynomial identity

`A(w) - D(w)·(1 + pΔ₁w + p²E₂w² + p³E₃w³) = p⁴·U(w)`

(coefficient comparison: the coefficients of `w⁰,…,w³` of the left side vanish by definition of
`Δ₁`, `E₂`, `E₃`, while those of `w⁴,w⁵,w⁶` are `p⁴·…`, `p⁵·…`, `p⁶·…` respectively), where

`U(w) = -(e₁(C)E₃ + e₂(C)E₂ + e₃(C)Δ₁) w⁴ - p (e₂(C)E₃ + e₃(C)E₂) w⁵ - p² e₃(C)E₃ w⁶`.

The denominator is itself a *polynomial* function of `w`: since `(p C_l w)^e = 0`,

`(1 + pC_l w)⁻¹ = ∑_{k<e} (-(pC_l w))^k`,

so `D(w)⁻¹ = ddBPoly.eval w` with `ddBPoly = ∏_l ∑_{k<e} (-(p C_l))^k X^k`.  Multiplying the
identity above by this polynomial, and using `D(w)·D(w)⁻¹ = 1`, gives
`p⁴·(ddUPoly·ddBPoly).eval w = Φ(w) - (1 + pΔ₁w + p²E₂w² + p³E₃w³)`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.LinnikBurgess

/-- The truncated geometric series `∑_{k<e} (-(x·X))^k ∈ R[X]`; its value at `w` is
`∑_{k<e} (-(x·w))^k`, an inverse of `1 + x·w` as soon as `(x·w)^e = 0`. -/
noncomputable def invSeriesPoly {R : Type*} [CommRing R] (e : ℕ) (x : R) : Polynomial R :=
  ∑ k ∈ Finset.range e, (-(Polynomial.C x * Polynomial.X)) ^ k

lemma invSeriesPoly_eval {R : Type*} [CommRing R] (e : ℕ) (x w : R) :
    (invSeriesPoly e x).eval w = ∑ k ∈ Finset.range e, (-(x * w)) ^ k := by
  rw [invSeriesPoly, Polynomial.eval_finsetSum]
  simp [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- `(1 + x) · ∑_{k<e} (-x)^k = 1` when `x^e = 0`. -/
lemma geom_sum_mul_one_add {R : Type*} [CommRing R] (e : ℕ) (x : R) (hx : x ^ e = 0) :
    (1 + x) * (∑ k ∈ Finset.range e, (-x) ^ k) = 1 := by
  have h := geom_sum_mul_neg (-x) e
  have hne : (-x) ^ e = 0 := by rw [neg_pow, hx, mul_zero]
  rw [show (1 : R) - (-x) = 1 + x by ring, hne, sub_zero] at h
  simpa [mul_comm] using h

/-- In `ZMod n`, `(1 + x)⁻¹ = ∑_{k<e} (-x)^k` when `x^e = 0`. -/
lemma inv_one_add_eq_geom_sum {n e : ℕ} (x : ZMod n) (hx : x ^ e = 0) :
    (1 + x)⁻¹ = ∑ k ∈ Finset.range e, (-x) ^ k :=
  ZMod.inv_eq_of_mul_eq_one n (1 + x) _ (geom_sum_mul_one_add e x hx)

/-- In `ZMod (p^e)`, `(p·y·w)^e = 0` — `p` is nilpotent. -/
lemma p_mul_pow_eq_zero {p e : ℕ} (y w : ZMod (p ^ e)) :
    ((p : ZMod (p ^ e)) * y * w) ^ e = 0 := by
  have hp : ((p : ZMod (p ^ e))) ^ e = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  rw [mul_pow, mul_pow, hp, zero_mul, zero_mul]

/-- The truncated geometric series inverts `1 + p·y·w` in `ZMod (p^e)`. -/
lemma geom_sum_inv_factor {p e : ℕ} (y w : ZMod (p ^ e)) :
    (∑ k ∈ Finset.range e, (-((p : ZMod (p ^ e)) * y * w)) ^ k)
      = (1 + (p : ZMod (p ^ e)) * y * w)⁻¹ := by
  rw [inv_one_add_eq_geom_sum _ (p_mul_pow_eq_zero y w)]

/-- The polynomial identity behind the level-`1` expansion: after clearing the denominator, the
first four coefficients cancel by definition of `Δ₁`, `E₂`, `E₃` and the remainder is `p⁴` times an
explicit polynomial (of degree `6`). -/
private lemma ring_key {p e : ℕ} (A C : Fin 3 → ZMod (p ^ e)) (w : ZMod (p ^ e)) :
    (∏ l : Fin 3, (1 + (p : ZMod (p ^ e)) * A l * w))
      - (∏ l : Fin 3, (1 + (p : ZMod (p ^ e)) * C l * w))
        * (1 + (p : ZMod (p ^ e)) * ddDsum p e 1 A C * w
           + (p : ZMod (p ^ e)) ^ 2 * ddE2 A C * w ^ 2
           + (p : ZMod (p ^ e)) ^ 3 * ddE3 A C * w ^ 3)
    = (p : ZMod (p ^ e)) ^ 4
        * (-((C 0 + C 1 + C 2) * ddE3 A C
              + (C 0 * C 1 + C 0 * C 2 + C 1 * C 2) * ddE2 A C
              + (C 0 * C 1 * C 2) * ddDsum p e 1 A C) * w ^ 4
          - (p : ZMod (p ^ e)) * ((C 0 * C 1 + C 0 * C 2 + C 1 * C 2) * ddE3 A C
              + (C 0 * C 1 * C 2) * ddE2 A C) * w ^ 5
          - (p : ZMod (p ^ e)) ^ 2 * ((C 0 * C 1 * C 2) * ddE3 A C) * w ^ 6) := by
  simp only [Fin.prod_univ_three, ddDsum, ddE2, ddE3, Fin.sum_univ_three, pow_one]
  ring

/-- The polynomial `∏_l ∑_{k<e} (-(p C_l))^k X^k`, whose value at `w` is
`∏_l (1 + p C_l w)⁻¹`. -/
noncomputable def ddBPoly (p e : ℕ) (C : Fin 3 → ZMod (p ^ e)) : Polynomial (ZMod (p ^ e)) :=
  ∏ l : Fin 3, invSeriesPoly e ((p : ZMod (p ^ e)) * C l)

/-- The residual polynomial `U`, the quotient of the cleared identity by `p⁴`. -/
noncomputable def ddUPoly (p e : ℕ) (A C : Fin 3 → ZMod (p ^ e)) : Polynomial (ZMod (p ^ e)) :=
  Polynomial.C (-((C 0 + C 1 + C 2) * ddE3 A C
      + (C 0 * C 1 + C 0 * C 2 + C 1 * C 2) * ddE2 A C
      + (C 0 * C 1 * C 2) * ddDsum p e 1 A C)) * Polynomial.X ^ 4
  + Polynomial.C (-((p : ZMod (p ^ e)) * ((C 0 * C 1 + C 0 * C 2 + C 1 * C 2) * ddE3 A C
      + (C 0 * C 1 * C 2) * ddE2 A C))) * Polynomial.X ^ 5
  + Polynomial.C (-((p : ZMod (p ^ e)) ^ 2 * ((C 0 * C 1 * C 2) * ddE3 A C)))
      * Polynomial.X ^ 6

lemma ddBPoly_eval {p e : ℕ} (C : Fin 3 → ZMod (p ^ e)) (w : ZMod (p ^ e)) :
    (ddBPoly p e C).eval w
      = ∏ l : Fin 3, ∑ k ∈ Finset.range e, (-((p : ZMod (p ^ e)) * C l * w)) ^ k := by
  rw [ddBPoly, Polynomial.eval_prod]
  simp [invSeriesPoly_eval]

lemma ddUPoly_eval {p e : ℕ} (A C : Fin 3 → ZMod (p ^ e)) (w : ZMod (p ^ e)) :
    (ddUPoly p e A C).eval w
      = -((C 0 + C 1 + C 2) * ddE3 A C
          + (C 0 * C 1 + C 0 * C 2 + C 1 * C 2) * ddE2 A C
          + (C 0 * C 1 * C 2) * ddDsum p e 1 A C) * w ^ 4
        - (p : ZMod (p ^ e)) * ((C 0 * C 1 + C 0 * C 2 + C 1 * C 2) * ddE3 A C
            + (C 0 * C 1 * C 2) * ddE2 A C) * w ^ 5
        - (p : ZMod (p ^ e)) ^ 2 * ((C 0 * C 1 * C 2) * ddE3 A C) * w ^ 6 := by
  rw [ddUPoly, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_pow, Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- `ddBPoly.eval w` is exactly the inverse of the denominator `∏_l (1 + p C_l w)`. -/
lemma prod_inv_eq_ddBPoly_eval {p e : ℕ} (C : Fin 3 → ZMod (p ^ e)) (w : ZMod (p ^ e)) :
    (ddBPoly p e C).eval w
      = ∏ l : Fin 3, (1 + (p : ZMod (p ^ e)) * C l * w)⁻¹ := by
  rw [ddBPoly_eval]
  exact Finset.prod_congr rfl (fun l _ => geom_sum_inv_factor (C l) w)

/-- The denominator and its inverse multiply to one. -/
lemma prod_mul_inv_prod_eq_one {p e : ℕ} [NeZero p]
    (C : Fin 3 → ZMod (p ^ e)) (w : ZMod (p ^ e)) :
    (∏ l : Fin 3, (1 + (p : ZMod (p ^ e)) * C l * w))
      * (∏ l : Fin 3, (1 + (p : ZMod (p ^ e)) * C l * w)⁻¹) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun l _ => ?_)
  refine ZMod.mul_inv_of_unit _ ?_
  have h := Commons.NumberTheory.DirichletCharacter.isUnit_one_add_pPow_mul (p := p) (e := e)
    (ℓ := 1) (by norm_num) (C l) w
  simpa [Commons.NumberTheory.DirichletCharacter.pPow] using h

theorem ddPhi_expansion {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (A C : Fin 3 → ZMod (p ^ e)) :
    ∃ G : Polynomial (ZMod (p ^ e)),
      ∀ n : ℕ, Commons.NumberTheory.DirichletCharacter.prodCoord3 p e 1 A C ((n : ℤ) : ZMod (p ^ e))
        = 1 + (p : ZMod (p ^ e)) * Work.LinnikBurgess.ddDsum p e 1 A C * ((n : ℤ) : ZMod (p ^ e))
          + (p : ZMod (p ^ e)) ^ 2 * Work.LinnikBurgess.ddE2 A C * ((n : ℤ) : ZMod (p ^ e)) ^ 2
          + (p : ZMod (p ^ e)) ^ 3 * Work.LinnikBurgess.ddE3 A C * ((n : ℤ) : ZMod (p ^ e)) ^ 3
          + (p : ZMod (p ^ e)) ^ 4 * G.eval ((n : ℤ) : ZMod (p ^ e)) := by
  refine ⟨ddUPoly p e A C * ddBPoly p e C, fun n => ?_⟩
  have key : ∀ w : ZMod (p ^ e),
      Commons.NumberTheory.DirichletCharacter.prodCoord3 p e 1 A C w
        = 1 + (p : ZMod (p ^ e)) * ddDsum p e 1 A C * w
          + (p : ZMod (p ^ e)) ^ 2 * ddE2 A C * w ^ 2
          + (p : ZMod (p ^ e)) ^ 3 * ddE3 A C * w ^ 3
          + (p : ZMod (p ^ e)) ^ 4 * (ddUPoly p e A C * ddBPoly p e C).eval w := by
    intro w
    have hkey := ring_key A C w
    have hBC := prod_inv_eq_ddBPoly_eval C w
    have hCB := prod_mul_inv_prod_eq_one C w
    have hstep : (p : ZMod (p ^ e)) ^ 4
        * ((ddUPoly p e A C).eval w * (ddBPoly p e C).eval w)
        = (∏ l : Fin 3, (1 + (p : ZMod (p ^ e)) * A l * w))
            * (∏ l : Fin 3, (1 + (p : ZMod (p ^ e)) * C l * w)⁻¹)
          - (1 + (p : ZMod (p ^ e)) * ddDsum p e 1 A C * w
             + (p : ZMod (p ^ e)) ^ 2 * ddE2 A C * w ^ 2
             + (p : ZMod (p ^ e)) ^ 3 * ddE3 A C * w ^ 3) := by
      rw [ddUPoly_eval, hBC, ← mul_assoc, ← hkey, sub_mul]
      rw [show (∏ l : Fin 3, (1 + (p : ZMod (p ^ e)) * C l * w))
              * (1 + (p : ZMod (p ^ e)) * ddDsum p e 1 A C * w
                 + (p : ZMod (p ^ e)) ^ 2 * ddE2 A C * w ^ 2
                 + (p : ZMod (p ^ e)) ^ 3 * ddE3 A C * w ^ 3)
              * (∏ l : Fin 3, (1 + (p : ZMod (p ^ e)) * C l * w)⁻¹)
            = (1 + (p : ZMod (p ^ e)) * ddDsum p e 1 A C * w
                 + (p : ZMod (p ^ e)) ^ 2 * ddE2 A C * w ^ 2
                 + (p : ZMod (p ^ e)) ^ 3 * ddE3 A C * w ^ 3)
              * ((∏ l : Fin 3, (1 + (p : ZMod (p ^ e)) * C l * w))
                 * (∏ l : Fin 3, (1 + (p : ZMod (p ^ e)) * C l * w)⁻¹)) by ring,
        hCB, mul_one]
    simp only [Commons.NumberTheory.DirichletCharacter.prodCoord3,
      Commons.NumberTheory.DirichletCharacter.pPow, pow_one]
    rw [Polynomial.eval_mul, hstep]
    ring
  exact key ((n : ℤ) : ZMod (p ^ e))

end Work.LinnikBurgess
