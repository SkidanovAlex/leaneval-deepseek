import Mathlib
import Submission.Work.TMC14Core.evenExpandContract
import Submission.Work.TMC14Core.deriv2ExpandTwo
import Submission.Work.TMC14Core.rootSignPositiveRoots
import Submission.Work.TMC14Core.contractTwoRootsPos

namespace Work.TMC14Core

/-- **Even root sign.**

Let `p : ℂ[X]` be a monic, non-constant polynomial which is even (`p(-z) = p(z)`), all of
whose roots are real, and with `p(0) ≠ 0`.  Then `p(0)` and `p''(0)` are real numbers of
opposite sign: in particular `p(0) · p''(0) < 0`.

The proof reduces `p` to the polynomial `q` with `p = q(X²)` (so `q = contract 2 p`):
`q` is monic, non-constant, `q(0) = p(0) ≠ 0`, and every root of `q` is a strictly positive
real (a root `z` of `q` has a square root `w`, and `z = w² = (re w)² ≥ 0` is real because
`w` is a root of `p`; it is nonzero because `q(0) ≠ 0`).  For such a `q` one computes
`q'(0) = q(0) · ∑_z 1/(0 - z) = q(0) · (-∑_z 1/z)`, a product of `q(0) ≠ 0` with a strictly
negative real number, whence `q(0)·q'(0) < 0`.  Since `p(0) = q(0)` and `p''(0) = 2 q'(0)`,
the claim follows. -/
theorem evenRootSign (p : Polynomial ℂ) (hmonic : p.Monic) (hdeg : p.natDegree ≠ 0)
    (heven : ∀ z : ℂ, p.eval (-z) = p.eval z)
    (hreal : ∀ z : ℂ, p.eval z = 0 → z.im = 0) (h0 : p.eval 0 ≠ 0) :
    (p.eval 0).im = 0 ∧ ((Polynomial.derivative (Polynomial.derivative p)).eval 0).im = 0 ∧
      (p.eval 0).re * ((Polynomial.derivative (Polynomial.derivative p)).eval 0).re < 0 := by
  -- Write `p = q(X²)` for `q = contract 2 p`.
  obtain ⟨q, hpq⟩ : ∃ q : Polynomial ℂ, p = Polynomial.expand ℂ 2 q :=
    ⟨Polynomial.contract 2 p, evenExpandContract p heven⟩
  have hqe : p.eval 0 = q.eval 0 := by
    rw [hpq, Polynomial.expand_eval]
    norm_num
  have hqmonic : q.Monic :=
    (Polynomial.monic_expand_iff (p := 2) (f := q) (by norm_num)).mp (hpq ▸ hmonic)
  have hqdeg : q.natDegree ≠ 0 := by
    have hpdeg : p.natDegree = q.natDegree * 2 := by
      rw [hpq, Polynomial.natDegree_expand]
    intro hc
    rw [hc, zero_mul] at hpdeg
    exact hdeg hpdeg
  have hq0 : q.eval 0 ≠ 0 := by rw [← hqe]; exact h0
  -- Every root of `q` is a strictly positive real.
  have hqpos : ∀ z ∈ q.roots, z.im = 0 ∧ 0 < z.re :=
    contractTwoRootsPos p q hpq hq0 hreal
  obtain ⟨h1, h2, h3⟩ := rootSignPositiveRoots q hqmonic hqdeg hq0 hqpos
  -- `p''(0) = 2 q'(0)`.
  have hder2 : (Polynomial.derivative (Polynomial.derivative p)).eval 0
      = 2 * (Polynomial.derivative q).eval 0 := by
    rw [hpq]
    exact deriv2ExpandTwo q
  have e1 : (2 : ℂ).re = 2 := by norm_num
  have e2 : (2 : ℂ).im = 0 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hqe]; exact h1
  · rw [hder2, Complex.mul_im, e1, e2, h2]; ring
  · rw [hqe, hder2, Complex.mul_re, e1, e2]
    nlinarith [h3]

end Work.TMC14Core
