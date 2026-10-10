import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

/-- General substitution computation in a commutative ring of characteristic two.

If `Y = s * B + p * Y₁` and
`Y² + (a₁ * p) * B * Y + B² * c = (a₁ * p)² * N`, then
`p² ∣ B² * (s * s + s * (a₁ * p) + c)`.

The quotient is `a₁² * N + Y₁² + a₁ * B * Y₁`. -/
lemma crux_gen {R : Type*} [CommRing R] [CharP R 2] (a₁ B Y Y₁ p c N s : R)
    (hY : Y = s * B + p * Y₁)
    (heq : Y ^ 2 + (a₁ * p) * B * Y + B ^ 2 * c = (a₁ * p) ^ 2 * N) :
    p ^ 2 ∣ B ^ 2 * (s * s + s * (a₁ * p) + c) := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  refine ⟨a₁ ^ 2 * N + Y₁ ^ 2 + a₁ * B * Y₁, ?_⟩
  subst hY
  ring_nf at heq ⊢
  simp only [h2, mul_zero, zero_add] at heq ⊢
  rw [← CharTwo.add_eq_zero]
  have key : s * B ^ 2 * p * a₁ + s ^ 2 * B ^ 2 + B ^ 2 * c
      + (B * p ^ 2 * Y₁ * a₁ + p ^ 2 * Y₁ ^ 2 + p ^ 2 * a₁ ^ 2 * N)
      = (s * B ^ 2 * p * a₁ + s ^ 2 * B ^ 2 + B * p ^ 2 * Y₁ * a₁ + B ^ 2 * c
          + p ^ 2 * Y₁ ^ 2)
        + p ^ 2 * a₁ ^ 2 * N := by ring
  rw [key, heq]
  exact CharTwo.add_self_eq_zero _

/-- Substitution computation in characteristic two: if `Y = C s * B + p * Y₁` and
`Y² + (C a₁ * p) * B * Y + B² * c = (C a₁ * p)² * N`, then
`p² ∣ B² * (C s * C s + C s * (C a₁ * p) + c)`. -/
theorem CruxSubst {L : Type*} [Field L] [CharP L 2] (a₁ : L) (B Y Y₁ p c N : Polynomial L) (s : L)
    (hY : Y = Polynomial.C s * B + p * Y₁)
    (heq : Y ^ 2 + (Polynomial.C a₁ * p) * B * Y + B ^ 2 * c
        = (Polynomial.C a₁ * p) ^ 2 * N) :
    p ^ 2 ∣ B ^ 2 * (Polynomial.C s * Polynomial.C s + Polynomial.C s * (Polynomial.C a₁ * p) + c) := by
  exact crux_gen (Polynomial.C a₁) B Y Y₁ p c N (Polynomial.C s) hY heq

end Work.MotC2
