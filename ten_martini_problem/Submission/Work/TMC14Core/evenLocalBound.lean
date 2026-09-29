import Mathlib
import Submission.Work.TMC14Core.evenLocalExpansion
import Submission.Work.TMC14Core.exists_delta_re_neg
import Submission.Work.TMC14Core.norm_le_of_im_zero_of_sq_re_le

namespace Work.TMC14Core

/-- **TMC14Core: local maximum of `‖p‖` at `0` in the even, real-on-`ℝ` case.**

Let `p : ℂ[X]` be even (`p(-z) = p(z)`) and real on the real axis, with `p(0) = c0`,
`p''(0) = c2` for real `c0, c2` of opposite signs.  Then `‖p(E)‖ ≤ ‖p(0)‖` for all real
`E` in a neighbourhood of `0`: `0` is a strict local maximum of `|p|`.

The proof extracts `b` with `p = C c0 + X² b` and `b(0) = c2/2` (evenness kills the odd
part), forms `Q = 2·C c0·b + X²·b²`, so that `p² - C(c0²) = X²·Q`, and notes
`Re Q(0) = c0·c2 < 0`.  Since `Q` is continuous, `Re Q` stays negative near `0`, whence
`Re (p(E)²) - c0² = E² · Re Q(E) ≤ 0`; realness of `p(E)` converts this into
`‖p(E)‖² ≤ c0² = ‖p(0)‖²`. -/
theorem evenLocalBound (p : Polynomial ℂ)
    (heven : ∀ z : ℂ, p.eval (-z) = p.eval z)
    (hreal : ∀ E : ℝ, (p.eval (E : ℂ)).im = 0)
    (c0 c2 : ℝ) (hc0 : p.eval (0 : ℂ) = (c0 : ℂ))
    (hc2 : (Polynomial.derivative (Polynomial.derivative p)).eval 0 = (c2 : ℂ))
    (hprod : c0 * c2 < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ E : ℝ, |E| < δ → ‖p.eval (E : ℂ)‖ ≤ ‖p.eval (0 : ℂ)‖ := by
  -- Evenness gives the expansion `p = C c0 + X² b` with `b(0) = c2/2`.
  obtain ⟨b, hb, hb0⟩ := evenLocalExpansion p heven c0 c2 hc0 hc2
  -- The auxiliary polynomial `Q = 2 c0 b + X² b²`, satisfying `p² - c0² = X² Q`.
  set Q : Polynomial ℂ :=
    (2 : Polynomial ℂ) * Polynomial.C (c0 : ℂ) * b + Polynomial.X ^ 2 * b ^ 2 with hQdef
  have hQid : p ^ 2 - (Polynomial.C (c0 : ℂ)) ^ 2 = Polynomial.X ^ 2 * Q := by
    rw [hQdef, hb]; ring
  -- `Re Q(0) = c0 c2 < 0`.
  have hQ0 : (Q.eval (0 : ℂ)).re < 0 := by
    have hQe : Q.eval (0 : ℂ) = ((c0 * c2 : ℝ) : ℂ) := by
      rw [hQdef]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_ofNat, hb0]
      push_cast
      ring
    rw [hQe, Complex.ofReal_re]
    exact hprod
  -- Continuity turns the sign at `0` into a neighbourhood.
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_re_neg Q hQ0
  refine ⟨δ, hδpos, ?_⟩
  intro E hE
  rw [hc0]
  have hQneg : (Q.eval (E : ℂ)).re < 0 := hδ E hE
  -- The evaluated identity `p(E)² - c0² = E² Q(E)`.
  have hid : (p.eval (E : ℂ)) ^ 2 - (c0 : ℂ) ^ 2 = (E : ℂ) ^ 2 * Q.eval (E : ℂ) := by
    have h := congrArg (Polynomial.eval (E : ℂ)) hQid
    simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X] using h
  -- Taking real parts: `Re (p(E)²) - c0² = E² · Re Q(E) ≤ 0`.
  have hkey : ((p.eval (E : ℂ)) ^ 2).re ≤ c0 ^ 2 := by
    have h2 := congrArg Complex.re hid
    rw [Complex.sub_re, ← Complex.ofReal_pow c0 2, Complex.ofReal_re,
      ← Complex.ofReal_pow E 2, Complex.re_ofReal_mul] at h2
    nlinarith [hQneg, sq_nonneg E]
  -- Convert to a norm inequality using realness of `p(E)`.
  exact norm_le_of_im_zero_of_sq_re_le (p.eval (E : ℂ)) c0 (hreal E) hkey

end Work.TMC14Core
