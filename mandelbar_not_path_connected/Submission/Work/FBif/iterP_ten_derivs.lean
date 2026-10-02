import Mathlib
import Submission.Work.FBif.IterPoly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Polynomial
open LeanEval.ComplexAnalysis (Tantibar)

namespace Work.FBif

/-! ## The tenth iterate as a composition

`(T_c)^[10] = (T_c)^[5] ∘ (T_c)^[5]`, and `(T_c)^[5] = z ↦ Q(z̄)` with `Q = iterP c 5`;
substituting, `(T_c)^[10] = Q ∘ (Q.map star)` as a polynomial identity. -/

private lemma iterP_ten_compid (c : ℂ) :
    iterP c 10 = (iterP c 5).comp ((iterP c 5).map (starRingEnd ℂ)) := by
  apply Polynomial.funext
  intro z
  rw [Polynomial.eval_comp, iterP_ten_eval]
  rw [show (10 : ℕ) = 5 + 5 from rfl, Function.iterate_add_apply]
  rw [← iterP_five_eval_star c ((Tantibar c)^[5] z)]
  rw [← iterP_five_eval_star c z]
  rw [star_eval]

/-- The first derivative of the tenth iterate as a polynomial. -/
private lemma iterP_ten_derivative (c : ℂ) :
    (iterP c 10).derivative =
      ((iterP c 5).derivative.map (starRingEnd ℂ)) *
        ((iterP c 5).derivative.comp ((iterP c 5).map (starRingEnd ℂ))) := by
  rw [iterP_ten_compid c, Polynomial.derivative_comp, Polynomial.derivative_map]

/-- The second derivative of the tenth iterate as a polynomial. -/
private lemma iterP_ten_derivative2 (c : ℂ) :
    (iterP c 10).derivative.derivative =
      (((iterP c 5).derivative.derivative.map (starRingEnd ℂ)) *
        ((iterP c 5).derivative.comp ((iterP c 5).map (starRingEnd ℂ))))
      + (((iterP c 5).derivative.map (starRingEnd ℂ)) *
        (((iterP c 5).derivative.map (starRingEnd ℂ)) *
          ((iterP c 5).derivative.derivative.comp
            ((iterP c 5).map (starRingEnd ℂ))))) := by
  have hA : Polynomial.derivative ((iterP c 5).derivative.map (starRingEnd ℂ))
      = (iterP c 5).derivative.derivative.map (starRingEnd ℂ) := by
    rw [Polynomial.derivative_map]
  have hB : Polynomial.derivative
        ((iterP c 5).derivative.comp ((iterP c 5).map (starRingEnd ℂ)))
      = ((iterP c 5).derivative.map (starRingEnd ℂ)) *
        ((iterP c 5).derivative.derivative.comp
          ((iterP c 5).map (starRingEnd ℂ))) := by
    rw [Polynomial.derivative_comp, Polynomial.derivative_map]
  rw [iterP_ten_derivative c, Polynomial.derivative_mul, hA, hB]

/-- The elementary algebra of the second derivative, with `M = 2 * A₂`. -/
private lemma deriv_alg (L M : ℂ) : star M * L + star L * (star L * M)
    = 2 * (L * star (M / 2) + M / 2 * (star L) ^ 2) := by
  have hdiv : star (M / 2) = star M / 2 := by
    rw [show (star : ℂ → ℂ) = ⇑(starRingEnd ℂ) from rfl, map_div₀, starRingEnd_apply,
      starRingEnd_apply]
    simp
  have h1 : star M = 2 * star (M / 2) := by rw [hdiv]; ring
  rw [h1]; ring

/-- **The first two derivatives of `(T_c)^[10]` at a period-`5` point.**

Let `(T_c)^[5] z₁ = z₁` and put `Q := Work.FBif.iterP c 5`, `lam := Q.derivative.eval (star z₁)`
and `A₂ := Q.derivative.derivative.eval (star z₁) / 2`.  Then the holomorphic polynomial
`Work.FBif.iterP c 10` of the tenth iterate (`Work.FBif.iterP_ten_eval`) satisfies

`(iterP c 10)' (z₁) = lam * star lam`   and
`(iterP c 10)'' (z₁) = 2 * (lam * star A₂ + A₂ * (star lam) ^ 2)`.

Suggested route.  `Work.FBif.iterP_five_eval_star` and `Work.FBif.iterP_ten_eval` say
`(iterP c 5).eval (star z) = (Tantibar c)^[5] z` and `(iterP c 10).eval z = (Tantibar c)^[10] z`
for all `z`; combining these with `(Tantibar c)^[10] z = (Tantibar c)^[5] ((Tantibar c)^[5] z)`
and `Work.FBif.star_eval` gives, pointwise, `(iterP c 10).eval z =
(iterP c 5).eval ((iterP c 5).map star).eval z`, so by `Polynomial.funext`

`iterP c 10 = (iterP c 5).comp ((iterP c 5).map star)`.

The hypothesis gives `Q.eval (star z₁) = z₁` (via `Work.FBif.iterP_five_eval_star`).  Then
differentiate with `Polynomial.derivative_comp` / `Polynomial.derivative_map`:

`(iterP c 10)' = (Q'.map star) * (Q'.comp (Q.map star))`,
`(iterP c 10)'' = (Q''.map star) * (Q'.comp (Q.map star)) + (Q'.map star) * ((Q''.comp (Q.map star)) * (Q'.map star))`.

Evaluating at `z₁` and using `Work.FBif.star_eval` (`(R.map star).eval z = star (R.eval (star z))`)
gives `(Q.map star).eval z₁ = star (Q.eval (star z₁)) = star z₁`, hence
`(Q'.map star).eval z₁ = star lam`, `(Q'.comp (Q.map star)).eval z₁ = lam`,
`(Q''.map star).eval z₁ = star (2 * A₂)` and `(Q''.comp (Q.map star)).eval z₁ = 2 * A₂`;
the two displayed identities follow by `ring`. -/
theorem iterP_ten_derivs (c z₁ : ℂ)
    (h5 : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁) :
    (Work.FBif.iterP c 10).derivative.eval z₁
        = (Work.FBif.iterP c 5).derivative.eval (star z₁) *
          star ((Work.FBif.iterP c 5).derivative.eval (star z₁)) ∧
      (Work.FBif.iterP c 10).derivative.derivative.eval z₁
        = 2 * ((Work.FBif.iterP c 5).derivative.eval (star z₁) *
              star ((Work.FBif.iterP c 5).derivative.derivative.eval (star z₁) / 2) +
            ((Work.FBif.iterP c 5).derivative.derivative.eval (star z₁) / 2) *
              (star ((Work.FBif.iterP c 5).derivative.eval (star z₁))) ^ 2) := by
  have hQeval : (iterP c 5).eval (star z₁) = z₁ := by
    rw [iterP_five_eval_star, h5]
  have hR : ((iterP c 5).map (starRingEnd ℂ)).eval z₁ = star z₁ := by
    rw [← star_eval, hQeval]
  have h1 : ((iterP c 5).derivative.map (starRingEnd ℂ)).eval z₁
      = star ((iterP c 5).derivative.eval (star z₁)) := by
    rw [← star_eval]
  have h2 : ((iterP c 5).derivative.comp
        ((iterP c 5).map (starRingEnd ℂ))).eval z₁
      = (iterP c 5).derivative.eval (star z₁) := by
    rw [Polynomial.eval_comp, hR]
  have h3 : ((iterP c 5).derivative.derivative.map (starRingEnd ℂ)).eval z₁
      = star ((iterP c 5).derivative.derivative.eval (star z₁)) := by
    rw [← star_eval]
  have h4 : ((iterP c 5).derivative.derivative.comp
        ((iterP c 5).map (starRingEnd ℂ))).eval z₁
      = (iterP c 5).derivative.derivative.eval (star z₁) := by
    rw [Polynomial.eval_comp, hR]
  constructor
  · rw [iterP_ten_derivative c, Polynomial.eval_mul, h1, h2]
    ring
  · rw [iterP_ten_derivative2 c, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_mul, h1, h2, h3, h4]
    exact deriv_alg _ _

end Work.FBif
