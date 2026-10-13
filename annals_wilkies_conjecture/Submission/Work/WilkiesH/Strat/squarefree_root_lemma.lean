import Mathlib

/-!
# The roots of the squarefree replacement

Given `C c * Q = D * G`, `D * W = C γ * G ^ n` (with `c, γ ≠ 0`) and a Bézout relation
`C lam = A * G + B * G'` (with `lam ≠ 0`), the polynomial `G` has exactly the same real roots as
`Q`, and all of them are simple.

* If `G t = 0` then `(D * G) t = 0`, hence `c * Q t = 0`, hence `Q t = 0`.
* Conversely, if `Q t = 0` then either `D t ≠ 0` and `(D * G) t = c * Q t = 0` gives `G t = 0`,
  or `D t = 0` and `(D * W) t = 0 = γ * G t ^ n` gives `G t = 0`.
* If moreover `G t = 0`, the Bézout relation gives `lam = B t * G' t`, so `G' t ≠ 0`.
-/

namespace Work.WilkiesH.Strat

theorem squarefree_root_lemma {Q G D W A B : Polynomial ℝ} {n : ℕ} {c γ lam : ℝ}
    (hc : c ≠ 0) (hγ : γ ≠ 0) (hlam : lam ≠ 0)
    (h1 : Polynomial.C c * Q = D * G)
    (h2 : D * W = Polynomial.C γ * G ^ n)
    (h3 : Polynomial.C lam = A * G + B * Polynomial.derivative G) :
    (∀ t : ℝ, G.eval t = 0 ↔ Q.eval t = 0) ∧
      (∀ t : ℝ, G.eval t = 0 → (Polynomial.derivative G).eval t ≠ 0) := by
  constructor
  · intro t
    have e1 := congrArg (Polynomial.eval t) h1
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at e1
    have e2 := congrArg (Polynomial.eval t) h2
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow] at e2
    constructor
    · intro hG
      rw [hG, mul_zero] at e1
      rcases mul_eq_zero.mp e1 with h | h
      · exact absurd h hc
      · exact h
    · intro hQ
      by_cases hD : D.eval t = 0
      · rw [hD, zero_mul] at e2
        have hpow : G.eval t ^ n = 0 := by
          rcases mul_eq_zero.mp e2.symm with h | h
          · exact absurd h hγ
          · exact h
        by_contra hG
        exact pow_ne_zero n hG hpow
      · rw [hQ, mul_zero] at e1
        rcases mul_eq_zero.mp e1.symm with h | h
        · exact absurd h hD
        · exact h
  · intro t hGt hd
    have e3 := congrArg (Polynomial.eval t) h3
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at e3
    rw [hGt, mul_zero, zero_add] at e3
    rw [hd, mul_zero] at e3
    exact hlam e3

end Work.WilkiesH.Strat
