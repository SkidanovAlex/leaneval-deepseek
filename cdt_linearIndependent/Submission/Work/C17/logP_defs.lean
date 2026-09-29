/-
# Definitions for `Work.C17.logP_not_holomorphic_at_xs`

The unlikely series `P = logP a b ra rb rab r0` (paper eq. (defP)) is written, under the
relation `(rabc)` (`hrel`), as a multiple of the overconvergent Hadamard product
`P_a = (H(a) − η_a A(a)) ⋆ A(b)` plus a remainder that converges on a strictly larger disc:

```
cₙ = κ·F n + K n,      κ = r_a + r_ab·η_b,   F n = dₙ(a)·uₙ(b),
K n = (r_b + r_ab·η_a)·uₙ(a)·dₙ(b) + r_ab·dₙ(a)·dₙ(b),
```

with `dₙ(a) = vₙ(a) − η_a·uₙ(a)` (`Submission.CDT.beukersD`) and
`uₙ = Submission.CDT.beukersUR`.  This module collects the definitions and the (purely
algebraic) coefficient identity, so that the lemmas about `F`, `K`, `κ` can be stated
independently of the main proof.
-/
import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.CRad.deps

namespace Work.C17

open scoped BigOperators

noncomputable section

/-- `κ = r_a + r_ab·η_b`: the coefficient of the overconvergent part `P_a` of `P`. -/
def kap (a b : ℚ) (ra rab : ℤ) : ℝ := (ra : ℝ) + (rab : ℝ) * Submission.CDT.beukersEta (b : ℝ)

/-- `F n = dₙ(a)·uₙ(b)`: the coefficients of `P_a = (H(a) − η_a A(a)) ⋆ A(b)`; they are all
negative and of the cusp growth `(1/xs)ⁿ`. -/
def Ffun (a b : ℚ) (n : ℕ) : ℝ :=
  Submission.CDT.beukersD (a : ℝ) n * Submission.CDT.beukersUR (b : ℝ) n

/-- `K n = P`-coefficient minus `κ·F n`: the remainder, of growth `xsⁿ`. -/
def Kfun (a b : ℚ) (ra rb rab : ℤ) (n : ℕ) : ℝ :=
  ((rb : ℝ) + (rab : ℝ) * Submission.CDT.beukersEta (a : ℝ)) *
      (Submission.CDT.beukersUR (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n)
    + (rab : ℝ) * (Submission.CDT.beukersD (a : ℝ) n * Submission.CDT.beukersD (b : ℝ) n)

/-- **The coefficient identity.** Under the relation `r_a η_a + r_b η_b + r_ab η_a η_b = r₀`, the
`n`-th coefficient of the unlikely series splits as `cₙ = κ·F n + K n`. -/
theorem logPCoeffQ_eq_kap_Ffun_add_Kfun (a b : ℚ) (ra rb rab r0 : ℤ)
    (hrel : (ra : ℝ) * Submission.CDT.beukersEta (a : ℝ)
        + (rb : ℝ) * Submission.CDT.beukersEta (b : ℝ)
        + (rab : ℝ) * (Submission.CDT.beukersEta (a : ℝ) * Submission.CDT.beukersEta (b : ℝ))
        = (r0 : ℝ))
    (n : ℕ) :
    ((Submission.CDT.logPCoeffQ a b ra rb rab r0 n : ℚ) : ℝ)
      = kap a b ra rab * Ffun a b n + Kfun a b ra rb rab n := by
  rw [kap, Ffun, Kfun]
  unfold Submission.CDT.logPCoeffQ Submission.CDT.beukersD
  push_cast
  rw [Submission.CDT.beukersUR_eq_cast, Submission.CDT.beukersVR_eq_cast,
      Submission.CDT.beukersUR_eq_cast, Submission.CDT.beukersVR_eq_cast]
  linear_combination
    ((Submission.CDT.beukersU a n : ℝ) * (Submission.CDT.beukersU b n : ℝ)) * hrel

end

end Work.C17
