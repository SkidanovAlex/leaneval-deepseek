/-
# `Submission.Work.FIArea5.S16Hecke.heckeLam_localInverse`

The **local Euler factor** of the Hecke `L`-function of `ℚ(i)` as a rational function of the local
parameter: with `a_ν := λ(p^ν)` the sequence of local Hecke eigenvalues at the prime `p`,

  `(Σ_ν a_ν z^ν) · (1 - a_1 z + (a_1² - a_2) z²) = 1`   for `‖z‖ < 1`.

Equivalently `Σ_ν λ(p^ν) T^ν = 1/(1 - λ(p)T + (λ(p)² - λ(p²))T²)`, the local factor of (16.17);
this is the analytic counterpart of the local recursion (16.30).

The proof combines three inputs, each proved in a sibling module:

* `tsum_mul_localFactor` — the general generating-function identity: a sequence `a` with
  `a_0 = 1`, `a_1 = A` and `a_{ν+2} = A a_{ν+1} - C a_ν` whose generating series converges satisfies
  `(Σ a_ν z^ν)(1 - A z + C z²) = 1`.  It is proved by an explicit partial-sum computation.
* `heckeLam_pow_bound` — the prime-power growth bound `‖λ(p^ν)‖ ≤ 4(ν+1)`, obtained from the
  general counting bound `heckeLam_bound` at the prime power `p^ν`.
* `summable_heckeLam_pow_mul` — absolute convergence of `Σ_ν λ(p^ν) z^ν` for `‖z‖ < 1`, which
  follows by comparison with `Σ (ν+1)‖z‖^ν`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.tsum_mul_localFactor
import Submission.Work.FIArea5.S16Hecke.heckeLam_pow_bound
import Submission.Work.FIArea5.S16Hecke.summable_heckeLam_pow_mul

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open scoped BigOperators

noncomputable section

/-- **Local Euler factor of the Hecke `L`-function** (the analytic form of the local recursion
(16.30)): for `‖z‖ < 1`,
`(Σ_{ν≥0} λ(p^ν) z^ν)·(1 - λ(p) z + (λ(p)² - λ(p²)) z²) = 1`. -/
theorem heckeLam_localInverse {chi : GaussianInt → ℂ} {k : ℤ} {p : ℕ} (hp : p.Prime)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (h1 : chi 1 = 1)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' e : ℕ, heckeLam chi k (p ^ e) * z ^ e)
      * (1 - heckeLam chi k p * z
          + ((heckeLam chi k p) ^ 2 - heckeLam chi k (p ^ 2)) * z ^ 2) = 1 := by
  -- the local recursion (16.30) at the prime `p`
  obtain ⟨hrec, _⟩ := heckeLam_localRec chi k p hp hmul hb
  -- absolute convergence of the local generating series for `‖z‖ < 1`
  have hsum : Summable (fun e : ℕ => heckeLam chi k (p ^ e) * z ^ e) :=
    summable_heckeLam_pow_mul hp hb hz
  -- normalisations `a_0 = 1`, `a_1 = λ(p)`
  have h0 : heckeLam chi k (p ^ 0) = 1 := by rw [pow_zero, heckeLam_one, h1]
  have hA : heckeLam chi k p = heckeLam chi k (p ^ 1) := by rw [pow_one]
  exact tsum_mul_localFactor (a := fun e : ℕ => heckeLam chi k (p ^ e))
    (A := heckeLam chi k p)
    (C := (heckeLam chi k p) ^ 2 - heckeLam chi k (p ^ 2)) hsum h0 hA hrec

end

end Work.FIArea5.S16Hecke
