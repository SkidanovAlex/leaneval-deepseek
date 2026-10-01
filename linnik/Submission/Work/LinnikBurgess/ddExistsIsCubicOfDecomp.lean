import Mathlib
import Submission.Work.LinnikBurgess.ddDefs

/-!
# Lifting a cubic `ZMod N`-phase to a genuine cubic integer polynomial

This file proves `Work.LinnikBurgess.ddExistsIsCubicOfDecomp`.

## The content

Let `W` be a polynomial over `ZMod N` of the shape

`W = w₁·X + w₂·X² + w₃·X³ + p·W'`   (`p : ℕ` reduced to `ZMod N`),

with the cubic coefficient `w₃` *not* divisible by `p` (i.e. `p ∤ w₃.val`).  Then the phase `W`,
viewed as a function `ℤ → ZMod N`, is the reduction of a *genuine cubic* integer phase:
there is `H : Polynomial ℤ` of the form

`H = β·X + γ·X² + δ·X³ + p·R`   with `p ∤ δ`

(`IsCubic p H`) whose reduction modulo `N` agrees with `W` on every integer.

This is the bookkeeping step that turns a phase already known to be a non-degenerate cube
modulo `p` (a `ZMod N`-polynomial) into an integer polynomial, so that the analytic bound
`cubic_phase_prime_pow` for `Tsum` can be applied to it.

## Proof

Choose the integer coefficients `β = w₁.val`, `γ = w₂.val`, `δ = w₃.val`: these are the
canonical lifts of `w₁, w₂, w₃`, and `p ∤ w₃.val` is exactly `¬ (p : ℤ) ∣ δ`.  It remains to
lift the "multiple of `p`" part: for any `W' : Polynomial (ZMod N)` there is `R : Polynomial ℤ`
with `R.eval n ≡ W'.eval n (mod N)` for all `n : ℤ`, namely the polynomial obtained by replacing
each coefficient by its canonical representative.  Such a lift exists by
`Polynomial.induction_on` (`0`, `C a`, sums, and the step `P ↦ P·X`).
-/

namespace Work.LinnikBurgess

/-- The canonical representative of `a : ZMod N`, read as an integer, reduces back to `a`. -/
private lemma zmod_intCast_val {N : ℕ} [NeZero N] (a : ZMod N) :
    ((a.val : ℤ) : ZMod N) = a := by
  rw [show ((a.val : ℤ) : ZMod N) = ((a.val : ℕ) : ZMod N) from by push_cast; ring]
  exact ZMod.natCast_zmod_val a

/-- Every polynomial over `ZMod N` is the reduction of an integer polynomial with the same
values on all integers. -/
private lemma exists_intPoly_lift {N : ℕ} [NeZero N] (W' : Polynomial (ZMod N)) :
    ∃ R : Polynomial ℤ, ∀ n : ℤ, ((R.eval n : ℤ) : ZMod N) = W'.eval ((n : ℤ) : ZMod N) := by
  induction W' using Polynomial.induction_on with
  | C a =>
      refine ⟨Polynomial.C (a.val : ℤ), fun n => ?_⟩
      simp only [Polynomial.eval_C]
      exact zmod_intCast_val a
  | add p q hp hq =>
      obtain ⟨Rp, hp'⟩ := hp
      obtain ⟨Rq, hq'⟩ := hq
      refine ⟨Rp + Rq, fun n => ?_⟩
      simp only [Polynomial.eval_add, Int.cast_add, hp' n, hq' n]
  | monomial n a ih =>
      obtain ⟨R, hR⟩ := ih
      refine ⟨R * Polynomial.X, fun m => ?_⟩
      simp only [Polynomial.eval_mul, Polynomial.eval_X, Int.cast_mul, hR m]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        pow_succ]
      ring

theorem ddExistsIsCubicOfDecomp {N p : ℕ} [NeZero N]
    (W W' : Polynomial (ZMod N)) (w₁ w₂ w₃ : ZMod N) (h3 : ¬ p ∣ w₃.val)
    (hW : W = Polynomial.C w₁ * Polynomial.X + Polynomial.C w₂ * Polynomial.X ^ 2
      + Polynomial.C w₃ * Polynomial.X ^ 3 + Polynomial.C (p : ZMod N) * W') :
    ∃ H : Polynomial ℤ, Work.LinnikBurgess.IsCubic p H ∧
      ∀ n : ℤ, ((H.eval n : ℤ) : ZMod N) = W.eval ((n : ℤ) : ZMod N) := by
  obtain ⟨R, hR⟩ := exists_intPoly_lift W'
  refine ⟨Polynomial.C (w₁.val : ℤ) * Polynomial.X + Polynomial.C (w₂.val : ℤ) * Polynomial.X ^ 2
    + Polynomial.C (w₃.val : ℤ) * Polynomial.X ^ 3 + Polynomial.C (p : ℤ) * R, ?_, ?_⟩
  · refine ⟨(w₁.val : ℤ), (w₂.val : ℤ), (w₃.val : ℤ), R, ?_, rfl⟩
    intro h
    exact h3 (Int.natCast_dvd_natCast.mp h)
  · intro n
    rw [hW]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow]
    push_cast
    rw [ZMod.natCast_zmod_val w₁, ZMod.natCast_zmod_val w₂, ZMod.natCast_zmod_val w₃, hR n]

end Work.LinnikBurgess
