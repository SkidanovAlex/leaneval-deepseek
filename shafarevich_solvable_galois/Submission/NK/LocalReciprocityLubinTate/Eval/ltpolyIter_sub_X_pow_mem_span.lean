import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionRing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `LTpolyIter π q n ≡ X ^ (q ^ n)` modulo `π`

The iterates of the standard Lubin–Tate polynomial `f(X) = πX + X^q` are congruent, modulo the
coefficient ideal `(π)`, to the pure monomial `X ^ (q ^ n)`: all coefficients of
`LTpolyIter π q n` other than the leading one are divisible by `π` (and the leading coefficient is
`1`).  Milne, *CFT*, §I.3 uses this to compute the reduction of the division polynomials, hence
the shape of the division tower.

The proof is the obvious congruence induction: reduction is a ring homomorphism, and
`f ≡ X^q (mod π)`, so `f^{(n+1)} = f^{(n)} ∘ f ≡ (X^{q^n}) ∘ X^q = X^{q^{n+1}} (mod π)`.
-/

universe u

namespace NK.LocalReciprocityLubinTate.Eval

open Polynomial

/-- Congruence-in-witness form: `LTpolyIter π q n = X ^ (q ^ n) + π * a` for a suitable
polynomial `a`. -/
private lemma LTpolyIter_sub_X_pow_eq_C_mul {A : Type u} [CommRing A] (π : A) (q n : ℕ) :
    ∃ a : Polynomial A,
      NK.LocalReciprocityLubinTate.LTpolyIter π q n = Polynomial.X ^ (q ^ n) + Polynomial.C π * a := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      rw [NK.LocalReciprocityLubinTate.LTpolyIter_zero, pow_zero, pow_one, mul_zero, add_zero]
  | succ n ih =>
      obtain ⟨a, ha⟩ := ih
      have hmul : q * q ^ n = q ^ (n + 1) := by rw [pow_succ, mul_comm]
      have hfx : Polynomial.C π * Polynomial.X
          = NK.LocalReciprocityLubinTate.LTpoly π q - Polynomial.X ^ q := by
        rw [NK.LocalReciprocityLubinTate.LTpoly]; ring
      have hdvd : Polynomial.C π ∣ (NK.LocalReciprocityLubinTate.LTpoly π q) ^ (q ^ n)
          - (Polynomial.X ^ q) ^ (q ^ n) :=
        dvd_trans ⟨Polynomial.X, hfx.symm⟩ (sub_dvd_pow_sub_pow _ _ _)
      obtain ⟨b, hb⟩ := hdvd
      have hfm : (NK.LocalReciprocityLubinTate.LTpoly π q) ^ (q ^ n)
          = Polynomial.X ^ (q ^ (n + 1)) + Polynomial.C π * b := by
        have h1 : (NK.LocalReciprocityLubinTate.LTpoly π q) ^ (q ^ n)
            = (Polynomial.X ^ q) ^ (q ^ n) + Polynomial.C π * b := by
          rw [← hb]; ring
        rwa [← pow_mul, hmul] at h1
      refine ⟨b + a.comp (NK.LocalReciprocityLubinTate.LTpoly π q), ?_⟩
      calc NK.LocalReciprocityLubinTate.LTpolyIter π q (n + 1)
          = (NK.LocalReciprocityLubinTate.LTpoly π q) ^ (q ^ n)
              + Polynomial.C π * (a.comp (NK.LocalReciprocityLubinTate.LTpoly π q)) := by
              rw [NK.LocalReciprocityLubinTate.LTpolyIter_succ, ha, add_comp, mul_comp, C_comp,
                X_pow_comp]
        _ = Polynomial.X ^ (q ^ (n + 1))
              + Polynomial.C π * (b + a.comp (NK.LocalReciprocityLubinTate.LTpoly π q)) := by
              rw [hfm]; ring

theorem ltpolyIter_sub_X_pow_mem_span {A : Type u} [CommRing A] (π : A) (q n : ℕ) (hq : 1 ≤ q) :
    NK.LocalReciprocityLubinTate.LTpolyIter π q n - Polynomial.X ^ (q ^ n)
      ∈ Ideal.span {Polynomial.C π} := by
  obtain ⟨a, ha⟩ := LTpolyIter_sub_X_pow_eq_C_mul π q n
  rw [Ideal.mem_span_singleton]
  exact ⟨a, by rw [ha]; ring⟩

end NK.LocalReciprocityLubinTate.Eval
