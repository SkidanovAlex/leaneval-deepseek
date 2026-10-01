import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorAux

/-!
# The local sieve factor, in factored form

The local factor of the Selberg sieve function `G(s,χ)` at a prime `p` is defined
(`Submission/Work/LinnikAreas/BGTZSetup.lean`) as

`sieveLocal χ₁ χ s p = (1 + χ₁(p)) · χ(p) p^{-s} - χ₁(p) · (χ(p) p^{-s})²`

with `χ₁(p)` read through the real part of `χ₁`.  For a **real (quadratic)** character `χ₁`
(`χ₁² = 1`), so that `(χ₁ p).re` really is `χ₁ p`, this collapses to the factored identity

`sieveLocal χ₁ χ s p = 1 - (1 - (χχ₁)(p) p^{-s}) · (1 - χ(p) p^{-s})`,

i.e. with `u = χ(p) p^{-s}` and `x = χ₁(p)` it is the elementary identity
`(1+x)u - x u² = 1 - (1 - xu)(1 - u)`.

This is the form in which the local factor appears in the Euler product of `G`: the two factors
`(1 - (χχ₁)(p) p^{-s})` and `(1 - χ(p) p^{-s})` are exactly the local factors of
`L(s,χχ₁)^{-1}` and `L(s,χ)^{-1}`.
-/

open DirichletCharacter Complex
open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

/-- A quadratic character (`χ₁² = 1`) of level `q` is real-valued: its value at `p` is the
real number `(χ₁ p).re`. -/
private lemma re_eq_of_sq_eq_one {q : ℕ} (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    (p : ℕ) :
    ((χ₁ ((p : ℕ) : ZMod q)).re : ℂ) = χ₁ ((p : ℕ) : ZMod q) := by
  have hquad : χ₁.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hχ₁
  rcases hquad (p : ZMod q) with h | h | h <;> rw [h] <;> simp

theorem DetSieveLocalEq {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {s : ℂ} {p : ℕ} (hp : p.Prime) :
    Work.LinnikAreas.BGTZ.sieveLocal χ₁ χ s p
      = 1 - (1 - (χ * χ₁) ((p : ℕ) : ZMod q) * ((p : ℂ) ^ (-s)))
          * (1 - χ ((p : ℕ) : ZMod q) * ((p : ℂ) ^ (-s))) := by
  have hreal : ((χ₁ ((p : ℕ) : ZMod q)).re : ℂ) = χ₁ ((p : ℕ) : ZMod q) :=
    re_eq_of_sq_eq_one χ₁ hχ₁ p
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmul : (χ * χ₁) ((p : ℕ) : ZMod q)
      = χ ((p : ℕ) : ZMod q) * χ₁ ((p : ℕ) : ZMod q) :=
    MulChar.mul_apply χ χ₁ _
  rw [Work.LinnikAreas.BGTZ.sieveLocal, hmul, hreal]
  rw [show (p : ℂ) ^ (-(2 * s)) = ((p : ℂ) ^ (-s)) ^ 2 from by
    rw [sq, ← Complex.cpow_add (-s) (-s) hp0]
    congr 1
    ring]
  ring

end Work.LinnikAreas.BGTZ
