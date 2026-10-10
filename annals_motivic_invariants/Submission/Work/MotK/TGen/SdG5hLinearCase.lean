import Mathlib
import Submission.Work.MotK.TGen.CruxAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.SdG5hLinearCase` — the linear-factor case of the crux

`Gg g₁ g₂ g₃ g₄ g₅ = g₁x₀⁵ + g₂x₁⁵ + g₃x₂⁵ + g₄x₀²x₁x₂² + g₅x₀x₁³x₂`.

If `Gg` is divisible by a linear form `x₀ + b x₁ + c x₂` and `g₂ g₃ ≠ 0`, then
`g₅² = 5 g₂ g₄`.  This is the "degree 1" half of the crux argument recorded in
`Submission/Work/MotK/TGen/CruxAux.lean`.

The proof: substituting the root `x₀ = -(b x₁ + c x₂)` kills the linear form, so the
substituted quintic vanishes.  Evaluating at `(x₁,x₂) = (1,0)` and `(0,1)` (i.e. at the
original points `(-b,1,0)` and `(-c,0,1)`) gives `g₂ = g₁b⁵`, `g₃ = g₁c⁵`, whence
`b, c ≠ 0`.  Dehomogenising (`x₂ = 1`, `r = c/b`) the vanishing quintic becomes
`-g₁b⁵(X+r)⁵ + g₂X⁵ + g₃ + g₄b²(X+r)²X - g₅b(X+r)X³ = 0`; comparing the coefficients of
`X⁴` and `X` gives `g₅ b = -5g₁b⁴c` and `g₄c² = 5g₁bc⁴`, and the conclusion follows. -/

namespace Work.MotK.TGen

theorem SdG5hLinearCase {K : Type} [Field K] (g1 g2 g3 g4 g5 b c : K)
    (h2 : g2 ≠ 0) (h3 : g3 ≠ 0) (H : MvPolynomial (Fin 3) K)
    (hfac : (MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1
        + MvPolynomial.C c * MvPolynomial.X 2) * H
      = Work.MotK.TGen.Gg g1 g2 g3 g4 g5) :
    g5 ^ 2 = 5 * g2 * g4 := by
  -- Evaluating the identity at `(-b, 1, 0)` kills the linear form and gives `g₁b⁵ = g₂`.
  have hgb : g1 * b^5 = g2 := by
    have h := congrArg (MvPolynomial.eval (fun i : Fin 3 => match i with
        | 0 => (-b : K) | 1 => 1 | 2 => 0)) hfac
    simp only [map_mul, map_add, MvPolynomial.eval_X, MvPolynomial.eval_C] at h
    simp only [Gg, map_add, map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X] at h
    simp at h
    rw [show (g1 * (-b)^5 : K) = -(g1 * b^5) by ring] at h
    exact neg_add_eq_zero.mp h.symm
  -- Evaluating at `(-c, 0, 1)` gives `g₁c⁵ = g₃`.
  have hgc : g1 * c^5 = g3 := by
    have h := congrArg (MvPolynomial.eval (fun i : Fin 3 => match i with
        | 0 => (-c : K) | 1 => 0 | 2 => 1)) hfac
    simp only [map_mul, map_add, MvPolynomial.eval_X, MvPolynomial.eval_C] at h
    simp only [Gg, map_add, map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X] at h
    simp at h
    rw [show (g1 * (-c)^5 : K) = -(g1 * c^5) by ring] at h
    exact neg_add_eq_zero.mp h.symm
  have hb : b ≠ 0 := by
    intro hb0
    exact h2 (by rw [← hgb, hb0]; ring)
  have hc : c ≠ 0 := by
    intro hc0
    exact h3 (by rw [← hgc, hc0]; ring)
  -- Substitute `x₀ ↦ -(b x₁ + c x₂)` into `K[x₁,x₂]` and dehomogenise (`x₂ ↦ 1`).
  set r : K := c / b with hr
  have hbr : b * r = c := by rw [hr]; field_simp
  let ψ : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
    MvPolynomial.aeval (fun i : Fin 3 => match i with
      | 0 => (-(Polynomial.C b * (Polynomial.X + Polynomial.C r)) : Polynomial K)
      | 1 => Polynomial.X
      | 2 => 1)
  have hψL : ψ (MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1
      + MvPolynomial.C c * MvPolynomial.X 2) = 0 := by
    simp only [ψ, map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.algebraMap_eq]
    rw [mul_add, ← Polynomial.C_mul, hbr]
    first | refl_ring1 | ring
  have hψ : ψ (Gg g1 g2 g3 g4 g5) = 0 := by
    have h := congrArg ψ hfac
    rw [map_mul, hψL, zero_mul] at h
    exact h.symm
  set P : Polynomial K :=
    - Polynomial.C (g1 * b^5) * (Polynomial.X + Polynomial.C r)^5
      + Polynomial.C g2 * Polynomial.X^5
      + Polynomial.C g3
      + Polynomial.C (g4 * b^2) * (Polynomial.X + Polynomial.C r)^2 * Polynomial.X
      - Polynomial.C (g5 * b) * (Polynomial.X + Polynomial.C r) * Polynomial.X^3 with hPdef
  have hP : ψ (Gg g1 g2 g3 g4 g5) = P := by
    rw [hPdef]
    simp only [ψ, Gg, map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    simp only [mul_pow, Polynomial.C_pow, ← Polynomial.C_mul, ← Polynomial.algebraMap_eq]
    ring_nf
  -- The two coefficients of `P` we need.
  have c4 : P.coeff 4 = -(5 * g1 * b^5 * r) - g5 * b := by
    rw [hPdef]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_add_C_pow, Polynomial.coeff_mul_X,
      Polynomial.coeff_mul_X_pow', Polynomial.coeff_C, Polynomial.coeff_X,
      ← Polynomial.C_neg, neg_mul]
    norm_num
    first | refl_ring1 | ring
  have c1 : P.coeff 1 = -(5 * g1 * b^5 * r^4) + g4 * b^2 * r^2 := by
    rw [hPdef]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_add_C_pow, Polynomial.coeff_mul_X,
      Polynomial.coeff_mul_X_pow', Polynomial.coeff_C, Polynomial.coeff_X,
      ← Polynomial.C_neg, neg_mul]
    norm_num
    first | refl_ring1 | ring
  have e4 : -(5 * g1 * b^5 * r) - g5 * b = 0 := by
    rw [← c4, ← hP, hψ]
    simp
  have e1 : -(5 * g1 * b^5 * r^4) + g4 * b^2 * r^2 = 0 := by
    rw [← c1, ← hP, hψ]
    simp
  have hb5r : b^5 * r = b^4 * c := by rw [hr]; field_simp
  have hb2r2 : b^2 * r^2 = c^2 := by rw [hr]; field_simp
  have hb5r4 : b^5 * r^4 = b * c^4 := by rw [hr]; field_simp
  have h45 : g5 * b = -(5 * g1 * b^4 * c) := by
    linear_combination (norm := first | refl_ring1 | ring1) (-1 : K) * e4 - (5 * g1) * hb5r
  have h41 : g4 * c^2 = 5 * g1 * b * c^4 := by
    linear_combination (norm := first | refl_ring1 | ring1) e1 - g4 * hb2r2 + (5 * g1) * hb5r4
  have hg5 : g5 = -5 * g1 * b^3 * c := by
    refine mul_right_cancel₀ hb ?_
    rw [h45]; ring
  have hg4 : g4 = 5 * g1 * b * c^2 := by
    refine mul_right_cancel₀ (pow_ne_zero 2 hc) ?_
    rw [h41]; ring
  rw [hg5, hg4, ← hgb]
  first | refl_ring1 | ring

end Work.MotK.TGen
